//
//  main.c
//  demand_assignment_2
//
//  Created by 鈴木大樹 on 2020/11/19.
//

/*複数台・容量制約付きver.*/

/*確認事項
 ・オブジェクト形式マクロ全部
 ・シミュレーション方法（モンテカルロ・シミュレーションか，需要全出しか）
 ・ファイル名
 ・計算する時間割引率（1だけか，3パターン全部やるか）
*/

/*インプットは以下の通り
 ・#defineで定義される定数全て
 ・in_network（デマンド交通のネットワークデータ）
 ・in_od（時間制約付きOD表）
 ・in_network2（需要側のネットワークデータ）
 ・out_simulation（シミュレーション結果を格納するためのファイル）
 ・out_revenue（収益を格納するためのファイル）
 ※（アドホック対応）デマンドの滞在リンクは必ず用意．需要側の滞在リンクに対して(demand[j].o / 10) * 1000 + (demand[j].o % 10) * 10で対応するように設定する．
*/

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <limits.h>
#include <math.h>
#include <float.h>
#include <unistd.h>

#define TRIALS 1000 //シミュレーションの回数
#define RESULT_OUT 0 //車両の動き等の結果をCSVで出力するか否か
#define VNUMBER 1 //車両の台数
#define CAPACITY 1 //車両1台の容量
#define SOLUTION 0 //後ろ向き帰納法…0，方策反復法…1，価値反復法…2
#define V_INITIAL 0 //方策反復法で使用する状態価値関数の初期値
#define MICRO 0.0001 //方策反復・価値反復の収束判定値
#define gamma_a 0.0 //時間割引率その1
#define gamma_b 0.5 //時間割引率その2
#define gamma_c 1.0 //時間割引率その3
#define b_service 1.5 //デマンド交通の効用の定数項
#define Tmax 8 //終端時刻
#define STEPTIME 5 //1タイムステップの時間（分）
#define F0 100 //初乗り運賃(円)
#define F 50 //距離別運賃(円)
#define mu 1 //gRLのスケールパラメータ
#define beta 1 //gRLの時間割引率
#define PI 3.141592654 //円周率
#define DENO 100 //強制終了対策

typedef struct network {
    int id;
    int o;
    int d;
    int num; //配列番号
    unsigned f; //運賃
    unsigned mincost_o; //需要側：出発地からの最小所要時間，サービス側：出発地までの所要時間
    unsigned mincost_d; //目的地までの最小所要時間
    unsigned short I; //サービス側の指示関数
    double v[Tmax + 1]; //即時効用の確定項
    unsigned short II[Tmax + 1]; //gRLの指示関数
    double V[Tmax + 1]; //期待最大効用
    double c; //サービス側のコスト
    struct network *next;
} Network;

typedef struct demand {
    int id;
    int o;
    int d;
    unsigned tb;
    unsigned te;
    double e;
    double beta_time; //時間に対するパラメータ
    double beta_fare; //運賃に対するパラメータ
    double beta_t; //時刻に対するパラメータ
    double beta_exp; //過去の経験を表すパラメータ
    struct demand *next;
} Demand;

typedef struct {
    Network link; //どこのリンクにいるか
    unsigned short *sf; //入札状況
} V_State; //車両の状態

typedef struct {
    unsigned t; //時刻
    V_State *vs;
    unsigned short presence; //その状態が可能かどうか
    double V; //状態価値関数
    unsigned long long id; //比較演算用
} State; //状態

typedef struct {
    Network nextlink; //次のリンク
    unsigned short *x; //予約の受理・棄却
    unsigned short presence; //その行動をとることができるかどうか
} V_Action; //車両1つの行動

typedef struct {
    State nowstate; //現在の状態
    V_Action *va; //車両ごとの行動
    unsigned short presence; //その行動が可能かどうか
    double r; //行動に対する即時報酬
    unsigned long long id; //比較演算用
} Action; //行動

typedef struct {
    State state; //状態に対して
    Action action; //最適方策に基づく行動
    unsigned long long actionnum;
} Policy; //最適方策

/*デマンド交通のネットワークデータの仮格納*/
Network *input_network(Network *linklist, char *in_network, int *number_of_links)
{
    FILE *fp;
    Network *tmp_list, *p;
    char title[256];
    int ret;
    int tmp_id, tmp_o, tmp_d, tmp_c;

    if((fp = fopen(in_network, "r")) == NULL) {
        printf("%sを開けません．\n", in_network);
        exit(0);
    }

    /*1行目の読み込み*/
    fscanf(fp, "%s", title);

    /*ネットワークデータを一旦リスト構造に格納（いきなり配列に格納しようとすると要素数が分からなくて無駄になりかねないので）*/
    *number_of_links = 0;
    while ((ret = fscanf(fp, "%d,%d,%d,%d", &tmp_id, &tmp_o, &tmp_d, &tmp_c)) != EOF) {
        tmp_list = (Network *)malloc(sizeof(Network));
        if (tmp_list == NULL) {
            puts("メモリ不足1");
            exit(0);
        }

        tmp_list->id = tmp_id;
        tmp_list->o = tmp_o;
        tmp_list->d = tmp_d;
        tmp_list->c = tmp_c;
        tmp_list->next = NULL;

        if (linklist == NULL) {
            linklist = tmp_list;
        } else {
            p = linklist;
            while (p->next != NULL) {
                p = p->next;
            }
            p->next = tmp_list;
        }

        (*number_of_links)++;
    }

    fclose(fp);
    
    printf("デマンド交通のリンク数：%d\n\n", *number_of_links);

    return linklist;
}

/*デマンド交通のネットワークデータを配列に格納*/
void set_network(Network *link, Network *linklist, char *in_network, int n)
{
    Network *p;
    int i = 0;

    /*リスト構造に仮格納したデータを配列に本格納*/
    for (p = linklist; p != NULL; p = p->next) {
        if (i >= n) {
            puts("リンクの配列の要素数が足りません．");
            exit(0);
        }
        
        link[i].id = p->id;
        link[i].o = p->o;
        link[i].d = p->d;
        link[i].c = p->c;
        link[i].num = i;

        i++;
    }

    if (i < n) {
        puts("リンク数が足りません．");
        exit(0);
    }

    printf("ネットワークデータ格納完了\n");

    return;
}

/*OD表の仮格納*/
Demand *input_demand(Demand *odlist, char *in_od, int *number_of_od)
{
    FILE *fp;
    Demand *tmp_list, *p;
    char title[256];
    int ret;
    int tmp_id, tmp_o, tmp_d, tmp_tb, tmp_te;
    double tmp_e, tmp_beta_time, tmp_beta_fare, tmp_beta_t, tmp_beta_exp;

    if((fp = fopen(in_od, "r")) == NULL) {
        printf("%sを開けません．\n", in_od);
        exit(0);
    }

    /*1行目の読み込み*/
    fscanf(fp, "%s", title);

    /*ネットワークデータを一旦リスト構造に格納（いきなり配列に格納しようとすると要素数が分からなくて無駄になりかねないので）*/
    *number_of_od = 0;
    while ((ret = fscanf(fp, "%d,%d,%d,%d,%d,%lf,%lf,%lf,%lf,%lf", &tmp_id, &tmp_o, &tmp_d, &tmp_tb, &tmp_te, &tmp_e, &tmp_beta_time, &tmp_beta_fare, &tmp_beta_t, &tmp_beta_exp)) != EOF) {
        tmp_list = (Demand *)malloc(sizeof(Demand));
        if (tmp_list == NULL) {
            puts("メモリ不足2");
            exit(0);
        }

        tmp_list->id = tmp_id;
        tmp_list->o = tmp_o;
        tmp_list->d = tmp_d;
        tmp_list->tb = tmp_tb;
        tmp_list->te = tmp_te;
        tmp_list->e = tmp_e;
        tmp_list->beta_time = tmp_beta_time;
        tmp_list->beta_fare = tmp_beta_fare;
        tmp_list->beta_t = tmp_beta_t;
        tmp_list->beta_exp = tmp_beta_exp;
        tmp_list->next = NULL;

        if (odlist == NULL) {
            odlist = tmp_list;
        } else {
            p = odlist;
            while (p->next != NULL) {
                p = p->next;
            }
            p->next = tmp_list;
        }

        (*number_of_od)++;
    }

    fclose(fp);
    
    printf("OD数：%d\n\n", *number_of_od);

    return odlist;
}

/*OD表を配列に格納*/
void set_demand(Demand *demand, Demand *odlist, char *in_od, int n)
{
    Demand *p;
    int i = 0;

    /*リスト構造に仮格納したデータを配列に本格納*/
    for (p = odlist; p != NULL; p = p->next) {
        if (i >= n) {
            puts("OD表の配列の要素数が足りません．");
            exit(0);
        }

        demand[i].id = p->id;
        demand[i].o = p->o;
        demand[i].d = p->d;
        demand[i].tb = p->tb;
        demand[i].te = p->te;
        demand[i].e = p->e;
        demand[i].beta_time = p->beta_time;
        demand[i].beta_fare = p->beta_fare;
        demand[i].beta_t = p->beta_t;
        demand[i].beta_exp = p->beta_exp;

        i++;
    }

    if (i < n) {
        puts("OD数が足りません．");
        exit(0);
    }
    
    printf("OD表格納完了\n");

    return;
}

/*状態数の計算*/
unsigned long long how_many_states(Demand *demand, Network *link, int n, int m)
{
    int k, i;
    unsigned t;
    unsigned long long tmp1, tmp2, tmp3;
    
    tmp3 = 0;
    for (t = 0; t <= Tmax; t++) {
        tmp1 = 1;
        for (k = 0; k < n; k++) {
            if ((int)t <= (int)demand[k].tb - 2) {
                tmp1 *= 1;
            } else if (t == demand[k].tb - 1) {
                tmp1 *= 2;
            } else if (t == demand[k].tb) {
                tmp1 *= (VNUMBER + 1);
            } else {
                tmp1 *= (2 * VNUMBER + 1);
            }
        }
        tmp2 = 1;
        for (i = 0; i < VNUMBER; i++) {
            tmp2 *= (unsigned long long)m;
        }
        
        tmp3 += (tmp1 * tmp2);
    }
    
    printf("状態数：%llu\n\n", tmp3);

    return tmp3;
}

/*状態の格納*/
void set_states(State *state, unsigned long long n1, Demand *demand, int n2, Network *link, int n3)
{
    int i, j, k, ii, kk;
    unsigned t;
    unsigned long long N1, N2;
    unsigned long long k1, k2, K1, K2;
    unsigned long long count;
    unsigned long long deno;
    unsigned num;
    
    count = 0;
    for (t = 0; t <= Tmax; t++) {
        N1 = 1;
        for (k = 0; k < n2; k++) {
            if ((int)t <= (int)demand[k].tb - 2) {
                N1 *= 1;
            } else if (t == demand[k].tb - 1) {
                N1 *= 2;
            } else if (t == demand[k].tb) {
                N1 *= (VNUMBER + 1);
            } else {
                N1 *= (2 * VNUMBER + 1);
            }
        } // N1はsf_iktの組み合わせ数（t固定）
        
        N2 = 1;
        for (i = 0; i < VNUMBER; i++) {
            N2 *= n3;
        } //N2はl_itの組み合わせ数（t固定）
        
        for (k1 = 0; k1 < N1; k1++) {
            for (k2 = 0; k2 < N2; k2++) {
                K1 = k1;
                K2 = k2;
                
                state[count].vs = (V_State *)malloc(sizeof(V_State) * VNUMBER);
                if (state[count].vs == NULL) {
                    printf("state[%llu].vsのメモリ確保に失敗しました．\n", count);
                    exit(EXIT_FAILURE);
                }
                for (j = 0; j < VNUMBER; j++) {
                    state[count].vs[j].sf = (unsigned short *)malloc(sizeof(unsigned short) * n2);
                    if (state[count].vs[j].sf == NULL) {
                        printf("state[%llu].vs[%d].sfのメモリ確保に失敗しました．\n", count, j);
                        exit(EXIT_FAILURE);
                    }
                }
                
                state[count].presence = 1;
                state[count].t = t;
                state[count].id = count;
                
                /*l_itの格納*/
                for (i = 0; i < VNUMBER; i++) {
                    deno = 1;
                    for (ii = i + 1; ii < VNUMBER; ii++) {
                        deno *= n3;
                    }
                    
                    if (K2 / deno >= n3) {
                        puts("K2 / denoの値が不正です．");
                        printf("K2 / deno = %llu\n", K2 / deno);
                        exit(EXIT_FAILURE);
                    } else {
                        state[count].vs[i].link = link[K2 / deno];
                    }
                    K2 %= deno;
                }
                
                /*sf_iktの格納*/
                for (k = 0; k < n2; k++) {
                    deno = 1;
                    for (kk = k + 1; kk < n2; kk++) {
                        if ((int)t <= (int)demand[kk].tb - 2) {
                            deno *= 1;
                        } else if (t == demand[kk].tb - 1) {
                            deno *= 2;
                        } else if (t == demand[kk].tb) {
                            deno *= (VNUMBER + 1);
                        } else {
                            deno *= (2 * VNUMBER + 1);
                        }
                    }
                    
                    if ((int)t <= (int)demand[k].tb - 2) {
                        for (i = 0; i < VNUMBER; i++) {
                            state[count].vs[i].sf[k] = 0;
                        }
                    } else if (t == demand[k].tb - 1) {
                        if (K1 / deno == 0) {
                            for (i = 0; i < VNUMBER; i++) {
                                state[count].vs[i].sf[k] = 0;
                            }
                        } else if (K1 /deno == 1) {
                            for (i = 0; i < VNUMBER; i++) {
                                state[count].vs[i].sf[k] = 1;
                            }
                        } else {
                            puts("K1 / denoの値が不正です．");
                            printf("K1 / deno = %llu\n", K1 / deno);
                            exit(EXIT_FAILURE);
                        }
                    } else if (t == demand[k].tb) {
                        if (K1 / deno == 0) {
                            for (i = 0; i < VNUMBER; i++) {
                                state[count].vs[i].sf[k] = 0;
                            }
                        } else if (K1 / deno > VNUMBER) {
                            puts("K1 / denoの値が不正です．");
                            printf("K1 / deno = %llu\n", K1 / deno);
                            exit(EXIT_FAILURE);
                        } else {
                            for (i = 0; i < VNUMBER; i++) {
                                if (i == K1 / deno - 1) {
                                    state[count].vs[i].sf[k] = 2;
                                } else {
                                    state[count].vs[i].sf[k] = 0;
                                }
                            }
                        }
                    } else {
                        if (K1 / deno == 0) {
                            for (i = 0; i < VNUMBER; i++) {
                                state[count].vs[i].sf[k] = 0;
                            }
                        } else if (K1 / deno > 2 * VNUMBER) {
                            puts("K1 / denoの値が不正です．");
                            printf("K1 / deno = %llu\n", K1 / deno);
                            exit(EXIT_FAILURE);
                        } else if (K1 / deno >= 1 && K1 / deno <= VNUMBER) {
                            for (i = 0; i < VNUMBER; i++) {
                                if (i == K1 / deno - 1) {
                                    state[count].vs[i].sf[k] = 2;
                                } else {
                                    state[count].vs[i].sf[k] = 0;
                                }
                            }
                        } else {
                            for (i = 0; i < VNUMBER; i++) {
                                if (i == K1 / deno - VNUMBER - 1) {
                                    state[count].vs[i].sf[k] = 3;
                                } else {
                                    state[count].vs[i].sf[k] = 0;
                                }
                            }
                        }
                    }
                    K1 %= deno;
                }
//                for (k = 0; k < n2; k++) {
//                    if (state[count].t != demand[k].tb - 1 && state[count].vs[0].sf[k] == 1) {
//                        puts("変です！");
//                        printf("state[%llu].t = %d\n", count, state[count].t);
//                        printf("demand[%d].tb - 1 = %d\n", k, demand[k].tb - 1);
//                        printf("state[%llu].vs[0].sf[%d] = %u\n", count, k, state[count].vs[0].sf[k]);
//                        putchar('\n');
//                    }
//                }
                
                count++;
            }
        }
    }
  
    if (count != n1) {
        puts("状態数が間違っています．");
        printf("count：%llu\n", count);
        printf("number_of_states：%llu\n\n", n1);
        exit(EXIT_FAILURE);
    }
    
    count = 0;
    for (j = 0; j < n1; j++) {
        for (i = 0; i < VNUMBER; i++) {
            num = 0;
            for (k = 0; k < n2; k++) {
                if (state[j].vs[i].sf[k] == 3) {
                    num++;
                }
            }
            if (num > CAPACITY) {
                state[j].presence = 0;
                break;
            }
        }
        
        if (state[j].presence) {
            count++;
        }
    }
    
    printf("可能な状態数：%llu\n", count);
    puts("状態の格納完了");

    return;
}

/*Dijkstra法．startからgoalまでの最短所要時間を返す*/
int dijkstra(int start, int goal, Network *link, int n) //prevは前回呼び出したときのn
{
    int i;
    int min, argmin;
    int past;
    int d[256], Q[256];
    
//    printf("%d\n", *prev);
//    printf("%d\n", n);
//
//    if (*prev == -1) {
//        puts("a");
//        d = (int *)malloc(sizeof(int) * n);
//        Q = (int *)malloc(sizeof(int) * n);
//        if (d == NULL || Q == NULL) {
//            puts("メモリ不足4.0");
//            exit(EXIT_FAILURE);
//        }
//    } else if (n != *prev) {
//        puts("b");
//        d2 = (int *)realloc(d, sizeof(int) * n);
//        Q2 = (int *)realloc(Q, sizeof(int) * n);
//        if (d2 == NULL || Q2 == NULL) {
//            puts("メモリ不足4.1");
//            exit(EXIT_FAILURE);
//        } else {
//            d = d2;
//            Q = Q2;
//        }
//    }
    
    /*初期化*/
    for (i = 0; i < n; i++) {
        Q[i] = 1;
        
        if (link[i].id == start) {
            d[i] = 0;
        } else {
            d[i] = INT_MAX;
        }
    }

    past = INT_MAX / 2;
    /*本計算*/
    while (1) {
        min = INT_MAX;
        argmin = n;
        for (i = 0; i < n; i++) {
            if (Q[i]) {
                if (d[i] <= min) {
                    min = d[i];
                    argmin = i;
                }
            }
        }
        if (argmin == n) {
            puts("Dijkstra法で最小コストのリンクが見つかりません．");
            exit(0);
        }
        
        if (link[argmin].id == goal) {
            break;
        }

        if (argmin == past) {
            puts("Dijkstra法で繰り返し発生");
            printf("argmin = %d\n", argmin);
            printf("id = %d\n", link[argmin].id);
            exit(0);
        }
        past = argmin;
        Q[argmin] = 0;

        for (i = 0; i < n; i++) {
            if (link[argmin].d == link[i].o) {
                if (d[i] > d[argmin] + 1) {
                    d[i] = d[argmin] + 1;
                }
            }
        }
    }

    return min;
}

/*行動の制約条件としての指示関数Iの決定・事前に全て1で初期化が必要！*/
void get_I_for_action(Network *link, int n1, Demand demand, int demandnum, V_State v_state, int t) //demandnumは配列の何番目か
{
    int i;
    int onum = -1, dnum = -1;
    
    for (i = 0; i < n1; i++) {
        if (link[i].id == (demand.o / 10) * 1000 + (demand.o % 10) * 10) { //アドホック
            onum = i; //O^L_kの配列番号の探索
        }
        if (link[i].id == (demand.d / 10) * 1000 + (demand.d % 10) * 10) { //アドホック
            dnum = i;
        }
    }
    if (onum == -1 || dnum == -1) {
        puts("onumまたはdnumが見つかりませんでした．");
        exit(EXIT_FAILURE);
    }

    /*最小所要時間を求める*/
    for (i = 0; i < n1; i++) {
        if (link[i].o == v_state.link.d) {
            link[i].mincost_o = dijkstra(link[i].id, link[onum].id, link, n1); //そのリンクから需要のOまでの所要時間．
            link[i].mincost_d = dijkstra(link[i].id, link[dnum].id, link, n1); //そのリンクから需要のDまでの所要時間．
        }
    }
    
    if (v_state.sf[demandnum] == 0 || v_state.sf[demandnum] == 1) {
        for (i = 0; i < n1; i++) {
            if (link[i].o != v_state.link.d) {
                link[i].I = 0; //乗車していないなら空間的接続条件のみ
            }
        }
    } else if (v_state.sf[demandnum] == 2) { //予約受理・未乗車の場合
        for (i = 0; i < n1; i++) {
            if (link[i].o != v_state.link.d) {
                link[i].I = 0;
            } else {
                if (link[i].o != link[onum].d) { //普通はこっち
                    if (t + link[i].mincost_o + dijkstra(link[onum].id, link[dnum].id, link, n1) > demand.te) {
                        link[i].I = 0; //出発地を通って目的地にたどり着く最小時間と比較
                    }
                } else { //遷移先のリンクで乗車する場合は，目的地までの所要時間を考えれば良い
                    if (t + link[i].mincost_d > demand.te - 1) {
                        link[i].I = 0;
                    }
                }
            }
        }
    } else if (v_state.sf[demandnum] == 3 && v_state.link.d != link[dnum].o) { //乗車中で，次の状態でも客が乗っている場合
        for (i = 0; i < n1; i++) {
            if (link[i].o != v_state.link.d) {
                link[i].I = 0;
            } else {
                if (link[i].mincost_d + t > demand.te - 1) {
                    link[i].I = 0;
                }
            }
        }
    } else { //乗車中だが，次の状態では客が乗っていない場合
        for (i = 0; i < n1; i++) {
            if (link[i].o != v_state.link.d) {
                link[i].I = 0; //空間的接続条件のみ
            }
        }
    }
    
    return;
}

/*状態と行動との組み合わせ数の計算*/
unsigned long long how_many_actions(Network *link, int n1, State *state, unsigned long long n3, Demand *demand, int n4)
{
    int k, l, i;
    unsigned long long tmp1, tmp2, tmp3;
    unsigned long long count, s;
    
    count = 0;
    for (s = 0; s < n3; s++) {
        tmp2 = 1;
        for (i = 0; i < VNUMBER; i++) {
            tmp1 = 0;
            for (l = 0; l < n1; l++) {
                if (state[s].vs[i].link.d == link[l].o) {
                    tmp1++;
                }
            }
            tmp2 *= tmp1; //リンクの空間的接続条件のみを配慮
        }
        
        tmp3 = 1;
        for (k = 0; k < n4; k++) {
            if (state[s].vs[0].sf[k] == 1) { //vs[0]が1だったら他も全部1
                tmp3 *= (VNUMBER + 1);
            } else { //vs[0]が0じゃなかったら0は含まれない
                tmp3 *= 1;
            }
        }
        
        count += tmp2 * tmp3;
    }
    
//    count = 0;
//    for (s = 0; s < n3; s++) {
//        tmp2 = 1;
//        for (i = 0; i < VNUMBER; i++) {
//            tmp1 = 0;
//            for (l = 0; l < n1; l++) {
//                link[l].I = 1;
//            }
//            for (k = 0; k < n4; k++) {
//                get_I_for_action(link, n1, demand[k], k, state[s].vs[i], state[s].t, d, Q);
//            }
//            for (l = 0; l < n1; l++) {
//                if (link[l].I) {
//                    tmp1++;
//                }
//            }
//            tmp2 *= tmp1; //これだと，ある状態のときにどの行動も取ることができないという事態が生じる→ダメ
//        }
//
//        tmp3 = 1;
//        for (k = 0; k < n4; k++) {
//            if (state[s].vs[0].sf[k] == 1) { //vs[0]が1だったら他も全部1
//                tmp3 *= (VNUMBER + 1);
//            } else { //vs[0]が0じゃなかったら0は含まれない
//                tmp3 *= 1;
//            }
//        }
//
//        count += tmp2 * tmp3;
//    }
    
    return count;
}

/*行動の列挙・格納*/
void set_action(Action *action, unsigned long long n1, Network *link, int n2, State *state, unsigned long long n3, Demand *demand, int n4) //n4はOD数
{
    int i, k, l, kk, ii;
    unsigned long long N1, N2, s, a, tmp1;
    unsigned long long count;
    unsigned long long k1, k2, K1, K2;
    unsigned long long deno;
    int count3, out;
//    int corres;

    count = 0;
    for (s = 0; s < n3; s++) {
        N1 = 1;
        N2 = 1;
        
        for (i = 0; i < VNUMBER; i++) {
            tmp1 = 0;
            for (l = 0; l < n2; l++) {
                if (state[s].vs[i].link.d == link[l].o) {
                    tmp1++;
                }
            }
            N1 *= tmp1;
        }
        
//        for (i = 0; i < VNUMBER; i++) {
//            tmp1 = 0;
//            for (l = 0; l < n2; l++) {
//                link[l].I = 1;
//            }
//            for (k = 0; k < n4; k++) {
//                get_I_for_action(link, n2, demand[k], k, state[s].vs[i], state[s].t, d, Q);
//            }
//            for (l = 0; l < n2; l++) {
//                if (link[l].I) {
//                    tmp1++;
//                }
//            }
//            N1 *= tmp1; //リンクの組み合わせ数
//        }
        
        for (k = 0; k < n4; k++) {
            if (state[s].vs[0].sf[k] == 1) { //vs[0]が1だったら他も全部1
                N2 *= (VNUMBER + 1);
            } else {
                N2 *= 1; //受理/棄却の組み合わせ数
            }
        }
        
        for (k1 = 0; k1 < N1; k1++) {
            for (k2 = 0; k2 < N2; k2++) {
                K1 = k1;
                K2 = k2;
                
                action[count].id = count;
                action[count].nowstate = state[s];
                action[count].presence = 1;
                
                action[count].va = (V_Action *)malloc(sizeof(V_Action) * VNUMBER);
                if (action[count].va == NULL) {
                    printf("action[%llu].vaのメモリ確保失敗\n", count);
                    exit(EXIT_FAILURE);
                }
                for (i = 0; i < VNUMBER; i++) {
                    action[count].va[i].x = (unsigned short *)malloc(sizeof(unsigned short) * n4);
                    if (action[count].va[i].x == NULL) {
                        printf("action[%llu].va[%d].xのメモリ確保失敗\n", count, i);
                        exit(EXIT_FAILURE);
                    }
                }
                
                for (i = 0; i < VNUMBER; i++) {
                    deno = 1;
                    for (ii = i + 1; ii < VNUMBER; ii++) {
                        tmp1 = 0;
                        for (l = 0; l < n2; l++) {
                            if (state[s].vs[ii].link.d == link[l].o) {
                                tmp1++;
                            }
                        }
                        
//                        for (l = 0; l < n2; l++) {
//                            link[l].I = 1;
//                        }
//                        for (k = 0; k < n4; k++) {
//                            get_I_for_action(link, n2, demand[k], k, state[s].vs[ii], state[s].t, d, Q);
//                        }
//                        for (l = 0; l < n2; l++) {
//                            if (link[l].I) {
//                                tmp1++;
//                            }
//                        }
                        deno *= tmp1; //リンクの組み合わせ数
                    }
                    
//                    for (l = 0; l < n2; l++) {
//                        link[l].I = 1;
//                    }
//                    for (k = 0; k < n4; k++) {
//                        get_I_for_action(link, n2, demand[k], k, state[s].vs[i], state[s].t, d, Q);
//                    }
                    count3 = 0;
                    for (l = 0; l < n2; l++) {
                        if (state[s].vs[i].link.d == link[l].o) {
                            if (count3 == K1 / deno) {
                                action[count].va[i].nextlink = link[l];
                            }
                            count3++;
                        }
                        
//                        if (link[l].I) {
//                            if (count3 == K1 / deno) {
//                                action[count].va[i].nextlink = link[l];
//                            }
//                            count3++;
//                        }
                    }
                    if (K1 / deno > count3) {
                        puts("K1 / denoの値が不正です-1");
                        printf("K1 / deno = %llu\n", K1 / deno);
                        exit(EXIT_FAILURE);
                    }
                    K1 %= deno;
                }
                
                for (k = 0; k < n4; k++) {
                    deno = 1;
                    for (kk = k + 1; kk < n4; kk++) {
                        if (state[s].vs[0].sf[kk] == 1) { //vs[0]が1だったら他も全部1
                            deno *= (VNUMBER + 1);
                        } else {
                            deno *= 1;
                        }
                    }
                    
                    if (state[s].vs[0].sf[k] == 1) {
                        if (K2 / deno > VNUMBER) {
                            puts("K2 / denoの値が不正です-2");
                            printf("K2 / deno = %llu\n", K2 / deno);
                            exit(EXIT_FAILURE);
                        } else if (K2 / deno >= 1 && K2 / deno <= VNUMBER) {
                            for (i = 0; i < VNUMBER; i++) {
                                if (i == K2 / deno - 1) {
                                    action[count].va[i].x[k] = 1;
                                } else {
                                    action[count].va[i].x[k] = 0;
                                }
                            }
                        } else {
                            for (i = 0; i < VNUMBER; i++) {
                                action[count].va[i].x[k] = 0;
                            }
                        }
                    } else {
                        if (K2 / deno != 0) {
                            puts("K2 / denoの値が不正です-3");
                            printf("k = %d\nK2 = %llu\ndeno = %llu\nN2 = %llu\n", k, K2, deno, N2); //
                            printf("K2 / deno = %llu\n", K2 / deno); //
                            exit(EXIT_FAILURE);
                        } else {
                            for (i = 0; i < VNUMBER; i++) {
                                action[count].va[i].x[k] = 0;
                            }
                        }
                    }
                    K2 %= deno;
                }
                count++;
            }
        }
    }
    
    if (count != n1) {
        puts("行動数が間違っています．");
        printf("count：%llu\n", count);
        printf("number_of_actions：%llu\n\n", n1);
        exit(EXIT_FAILURE);
    }

    /*presenceと即時報酬の格納．不可能なactionはpresenceを0にする．*/
    count = 0;
    for (a = 0; a < n1; a++) {
        if (action[a].nowstate.t == Tmax) {
            action[a].presence = 0; //終端時刻に行動をとらない
            continue;
        }
        
        if (!action[a].nowstate.presence) {
            action[a].r = -DBL_MAX;
            continue;
        }
        
        out = 0;
        for (i = 0; i < VNUMBER; i++) {
            for (l = 0; l < n2; l++) {
                link[l].I = 1;
            }
            for (k = 0; k < n4; k++) {
                get_I_for_action(link, n2, demand[k], k, action[a].nowstate.vs[i], action[a].nowstate.t);
            }
            
            if (link[action[a].va[i].nextlink.num].I == 0) {
                action[a].r = -DBL_MAX;
                out = 1;
                break;
            }
        }
        if (out) {
            continue;
        }
        
        action[a].r = 0.0;
        for (i = 0; i < VNUMBER; i++) {
            for (k = 0; k < n4; k++) {
                int onum = -1, dnum = -1;
                for (l = 0; l < n2; l++) {
                    if (link[l].id == (demand[k].o / 10) * 1000 + (demand[k].o % 10) * 10) { //アドホック
                        onum = l; //O^L_kの配列番号の探索
                    }
                    if (link[l].id == (demand[k].d / 10) * 1000 + (demand[k].d % 10) * 10) { //アドホック
                        dnum = l;
                    }
                }
                if (onum == -1 || dnum == -1) {
                    puts("onumまたはdnumが見つかりませんでした．");
                    exit(EXIT_FAILURE);
                }
                action[a].r += action[a].va[i].x[k] * (F0 + F * dijkstra(link[onum].id, link[dnum].id, link, n2));
            }
            action[a].r -= action[a].va[i].nextlink.c;
        }
        count++;
        
//        if (action[a].nowstate.id == 1231) { //追加
//            for (i = 0; i < VNUMBER; i++) {
//                printf("action[%llu].va[%d].nextlink.id = %d\n", a, i, action[a].va[i].nextlink.id);
//                for (k = 0; k < n4; k++) {
//                    printf("action[%llu].va[%d].x[%d] = %u\n", a, i, k, action[a].va[i].x[k]);
//                }
//            }
//            printf("action[%llu].r = %f\n", a, action[a].r);
//            putchar('\n');
//        }
    }
    
//    for (a = 0; a < n1; a++) {
//        corres = 1;
//        if (action[a].nowstate.vs[0].link.id != 1020) {
//            corres = 0;
//        }
//        if (action[a].nowstate.vs[0].sf[0] != 0 || action[a].nowstate.vs[0].sf[1] != 3 || action[a].nowstate.vs[0].sf[2] != 3 || action[a].nowstate.vs[0].sf[3] != 0 || action[a].nowstate.vs[0].sf[4] != 0 || action[a].nowstate.vs[0].sf[5] != 0 || action[a].nowstate.vs[0].sf[6] != 0) {
//            corres = 0;
//        }
//        if (action[a].nowstate.t != 6) {
//            corres = 0;
//        }
//        if (corres) {
//            printf("action[%llu].va[0].nextlink.id = %d\n", a, action[a].va[0].nextlink.id);
//            for (k = 0; k < n4; k++) {
//                printf("action[%llu].va[0].x[%d] = %u\n", a, k, action[a].va[0].x[k]);
//            }
//            printf("action[%llu].r = %f\n", a, action[a].r);
//        }
//    }
    
    printf("可能な行動数：%llu\n", count);
    puts("行動と即時報酬の格納完了");

    return;
}

/*需要側のネットワークデータの仮格納*/
Network *input_network2(Network *linklist2, char *in_network2, int *number_of_links2)
{
    FILE *fp;
    Network *tmp_list, *p;
    char title[256];
    int ret;
    int tmp_id, tmp_o, tmp_d, tmp_f;

    if((fp = fopen(in_network2, "r")) == NULL) {
        printf("%sを開けません．\n", in_network2);
        exit(0);
    }

    /*1行目の読み込み*/
    fscanf(fp, "%s", title);

    /*ネットワークデータを一旦リスト構造に格納（いきなり配列に格納しようとすると要素数が分からなくて無駄になりかねないので）*/
    *number_of_links2 = 0;
    while ((ret = fscanf(fp, "%d,%d,%d,%d", &tmp_id, &tmp_o, &tmp_d, &tmp_f)) != EOF) {
        tmp_list = (Network *)malloc(sizeof(Network));
        if (tmp_list == NULL) {
            puts("メモリ不足6");
            exit(0);
        }

        tmp_list->id = tmp_id;
        tmp_list->o = tmp_o;
        tmp_list->d = tmp_d;
        tmp_list->f = tmp_f;
        tmp_list->next = NULL;

        if (linklist2 == NULL) {
            linklist2 = tmp_list;
        } else {
            p = linklist2;
            while (p->next != NULL) {
                p = p->next;
            }
            p->next = tmp_list;
        }

        (*number_of_links2)++;
    }

    fclose(fp);

    printf("需要側のリンク数：%d\n\n", *number_of_links2);

    return linklist2;
}

/*デマンド交通のネットワークデータを配列に格納*/
void set_network2(Network *link2, Network *linklist2, char *in_network2, int n)
{
    Network *p;
    int i = 0;

    /*リスト構造に仮格納したデータを配列に本格納*/
    for (p = linklist2; p != NULL; p = p->next) {
        if (i >= n) {
            puts("リンクの配列の要素数が足りません．");
            exit(EXIT_FAILURE);
        }

        link2[i].id = p->id;
        link2[i].o = p->o;
        link2[i].d = p->d;
        link2[i].f = p->f;

        i++;
    }

    if (i < n) {
        puts("リンク数が足りません．");
        exit(EXIT_FAILURE);
    }

    printf("需要側のネットワークデータ格納完了\n");

    return;
}

/*指示関数Iの決定（gRL）*/
void get_I(Network *link3, int n1, Demand demand)
{
    int i, t;

    /*最小所要時間を求める*/
    for (i = 0; i < n1; i++) {
        link3[i].mincost_o = dijkstra(demand.o, link3[i].id, link3, n1); //O_iから現在地までの最短時間
        link3[i].mincost_d = dijkstra(link3[i].id, demand.d, link3, n1); //現在地からD_iまでの最短時間
    }
    
    /*指示関数Iを決定*/
    for (i = 0; i < n1; i++) {
        for (t = 0; t <= Tmax; t++) {
            if (link3[i].mincost_o + demand.tb - 1 <= t && t + link3[i].mincost_d <= demand.te) {
                link3[i].II[t] = 1;
            } else {
                link3[i].II[t] = 0;
            }
        }
    }

    return;
}

/*後ろ向き帰納法で期待最大効用を求める（gRL）*/
void backward_induction_for_grl(Network *link3, int n1, Demand demand, int num2)
{
    int i, j, t;
    int dnumber = -1;
    double M2[Tmax + 1][n1][n1];
    double suminlog;
    
    /*前準備．t_i^B - 1においてO_iと待ちリンク以外の即時効用を-∞にする*/
    for (i = 0; i < n1; i++) {
        if (link3[i].id != demand.o && i < n1 - num2) { //i >= n1 - num2は待ちリンク
            link3[i].v[demand.tb - 1] = -DBL_MAX;
        }
    }
    
    /*Step 1*/
    for (i = 0; i < n1; i++) {
        if (link3[i].id == demand.d) {
            dnumber = i;
        }
    }
    if (dnumber == -1) {
        puts("目的地ダミーリンクが見つかりませんでした．");
        exit(0);
    }

    for (t = demand.tb - 1; t <= demand.te; t++) {
        link3[dnumber].V[t] = 0; //目的地ダミーリンクの期待最大効用は0
    }

    for (t = demand.tb - 1; t <= demand.te; t++) {
        for (i = 0; i < n1; i++) {
            for (j = 0; j < n1; j++) {
                if (link3[i].d == link3[j].o) {
                    M2[t][i][j] = link3[i].II[t] * link3[j].II[t + 1] * pow(M_E, link3[j].v[t] / mu);
                } else {
                    M2[t][i][j] = 0;
                }
            }
        }
    }

    /*Step 2*/
    t = demand.te;
    for (i = 0; i < n1; i++) {
        link3[i].V[t] = 0;
    }

    /*Step 3*/
    while (t != demand.tb - 1) {
        t -= 1;
        for (i = 0; i < n1; i++) {
            suminlog = 0;

            if (t == demand.te || i == dnumber) {
                link3[i].V[t] = 0;
            } else {
                for (j = 0; j < n1; j++) {
                    suminlog += M2[t][i][j] * pow(M_E, beta * link3[j].V[t + 1] / mu);
                }

                if (suminlog == 0) {
                    link3[i].V[t] = 0;
                } else {
                    link3[i].V[t] = mu * log(suminlog);
                }
            }
        }
    }

    return;
}

/*遷移確率行列を求める（gRL）*/
void get_prob_matrix(Network *link3, int n1, Demand demand, double *pr)
{
    double deno;
    int t, i, j;
    
    for (t = demand.tb - 1; t <= demand.te; t++) {
        for (i = 0; i < n1; i++) {
            deno = 0;

            for (j = 0; j < n1; j++) {
                if (link3[i].d == link3[j].o) {
                    deno += link3[i].II[t] * link3[j].II[t + 1] * pow(M_E, (link3[j].v[t] + beta * link3[j].V[t + 1]) / mu);
                    //if (pow(M_E, (link3[j].v[t] + beta * link3[j].V[t + 1]) / mu) > 0) {
                    //    puts("a");
                    //    printf("link3[%d].II[%d] = %d\n", i, t, link3[i].II[t]);
                    //    printf("link3[%d].II[%d] = %d\n", j, t + 1, link3[j].II[t + 1]);
                    //    printf("link3[%d].v[%d] = %f\n", j, t, link3[j].v[t] + beta * link3[j].V[t + 1]);
                    //}
                }
            }
            //printf("deno = %f\n", deno);

            for (j = 0; j < n1; j++) {
                if (link3[i].d != link3[j].o || link3[i].II[t] == 0 || link3[j].II[t + 1] == 0) {
                    pr[n1 * n1 * t + n1 * i + j] = 0;
                } else if (link3[i].id == demand.d) {
                    pr[n1 * n1 * t + n1 * i + j] = 0;
                    pr[n1 * n1 * t + n1 * i + i] = 1; //目的地に着いたら他のリンクには移動しない
                } else {
                    if (deno == 0) {
                        puts("gRLの選択確率の分母が0です．");
                        exit(EXIT_FAILURE);
                    }
                    pr[n1 * n1 * t + n1 * i + j] = pow(M_E, (link3[j].v[t] + beta * link3[j].V[t + 1]) / mu) / deno;
                }
                //if (t == demand.tb - 1) {
                    //printf("link3[%d].v[%d] = %f\n", j, t, link3[j].v[t]);
                    //printf("link3[%d].V[%d] = %f\n", j, t + 1, link3[j].V[t + 1]);
                //    printf("pr[%d][%d][%d] = %f\n", t, i, j, pr[n1 * n1 * t + n1 * i + j]);
                //}
            }
        }
    }

    return;
}

/*需要ごとにデマンド交通リンクを追加し，gRLで配分し，入札確率を求める*/
/*デマンド交通のリンクの位置(id)を与えて入札確率を返す*/
void grl_assignment(Network *link2, int n1, Demand *demand, int n2, Network *link, int n3, Action action, double *P)
{
    int i, j, t;
    int num1; //デマンド交通リンクの本数
    int num2; //待ちリンクの本数
    int N; //link3の要素数
    int idmax = INT_MAX; //変えないこと
    int nidmax = INT_MAX;
    int onum, dnum;
    double tmp;
    Network link3[256];
    double pr[2048];

    for (i = 0; i < n2; i++) { //全ての需要についての繰り返し
        /*----------デマンド交通リンクと待ちリンクを追加してリンクデータを完成----------*/
        num1 = (int)(demand[i].e * (dijkstra((demand[i].o / 10) * 1000 + (demand[i].o % 10) * 10, (demand[i].d / 10) * 1000 + (demand[i].d % 10) * 10, link, n3) - 1));
        
        tmp = 0.0;
        for (j = 0; j < VNUMBER; j++) {
            tmp += demand[i].e * dijkstra(action.va[j].nextlink.id, (demand[i].o / 10) * 1000 + (demand[i].o % 10) * 10, link, n3);
        }
        tmp /= VNUMBER;
        if (tmp <= 1) {
            num2 = 1;
        } else {
            num2 = tmp - 1;
        }
        
        N = n1 + num1 + num2;
//        link3 = (Network *)realloc(link3, sizeof(Network) * N);
//        pr = (double * )realloc(pr, sizeof(double) * N * N * (Tmax + 1));
//        if (link3 == NULL || pr == NULL) {
//            puts("メモリ不足7");
//            exit(EXIT_FAILURE);
//        }

        onum = -1;
        dnum = -1;
        for (j = 0; j < n1; j++) {
            if (link2[j].id == demand[i].o) {
                onum = j;
            }
            if (link2[j].id == demand[i].d) {
                dnum = j;
            }
        }
        if (onum == -1 || dnum == -1) {
            puts("onumまたはdnumが見つかりません．");
            exit(EXIT_FAILURE);
        }

        /*デマンド交通リンク以外はlink2の複製で良い・ついでに即時効用の格納*/
        for (j = 0; j < n1; j++) {
            link3[j] = link2[j];
            for (t = 0; t <= Tmax; t++) {
                link3[j].v[t] = demand[i].beta_time * STEPTIME + demand[i].beta_fare * link3[j].f;
            }
            if (link3[j].o != link3[j].d) {
                link3[j].v[demand[i].tb - 1] = -DBL_MAX;
            }
        }
        
        /*デマンド交通のネットワーク*/
        link3[n1].id = idmax - num1 + 1;
        link3[n1].o = -nidmax;
        link3[n1].d = nidmax - num1 + 1;
        for (t = 0; t <= Tmax; t++) { //1本目
            link3[n1].v[t] = demand[i].beta_time * STEPTIME; //料金は先払いなので時間のみ
        }
        if (num1 == 1) {
            link3[n1].d = link3[dnum].o;
        }
        
        for (j = n1 + 1; j < n1 + num1; j++) { //2本目以降
            link3[j].id = link3[j - 1].id + 1;
            link3[j].o = link3[j - 1].d;
            if (j != n1 + num1 - 1) {
                link3[j].d = link3[j - 1].d + 1;
            } else {
                link3[j].d = link3[dnum].o;
            }
            
            for (t = 0; t < Tmax; t++) {
                link3[j].v[t] = demand[i].beta_time * STEPTIME; //料金は先払いなので時間のみ
            }
        }
        
        /*待ちリンク*/
        link3[n1 + num1].id = idmax - num1 - num2 + 1;
        link3[n1 + num1].o = link3[onum].d;
        link3[n1 + num1].d = nidmax - num1 - num2 + 1;
        for (t = 0; t < Tmax; t++) { //1本目
            if (t == demand[i].tb - 1) {
                link3[n1 + num1].v[t] = b_service + demand[i].beta_time * STEPTIME + demand[i].beta_fare * (F0 + F * num1) + demand[i].beta_exp; //料金は先払い・経験による信頼度も含めて判断・定数項もここで固定で効いてくる
            } else {
                link3[n1 + num1].v[t] = -DBL_MAX;
            }
        }
        if (num2 == 1) {
            link3[n1 + num1].d = link3[n1].o;
        }
        
        for (j = n1 + num1 + 1; j < n1 + num1 + num2; j++) { //2本目以降
            link3[j].id = link3[j - 1].id + 1;
            link3[j].o = link3[j - 1].d;
            if (j != n1 + num1 + num2 - 1) {
                link3[j].d = link3[j - 1].d + 1;
            } else {
                link3[j].d = link3[n1].o;
            }
            
            for (t = 0; t < Tmax; t++) {
                link3[j].v[t] = demand[i].beta_time * STEPTIME; //料金は先払いなので時間のみ
            }
        }
        
        /*--------------------ここからgRLで配分--------------------*/
        /*指示関数の決定*/
        get_I(link3, N, demand[i]);

        /*期待最大効用を求める*/
        backward_induction_for_grl(link3, N, demand[i], num2);

        /*遷移確率行列を求める*/
        get_prob_matrix(link3, N, demand[i], pr);

        /*入札確率を格納*/
        for (t = 0; t <= Tmax; t++) {
            if (t == demand[i].tb - 1) {
                P[(Tmax + 1) * i + t] = pr[N * N * t + N * onum + n1 + num1];
                //printf("%f\n", P[(Tmax + 1) * i + t]);
                //if (P[(Tmax + 1) * i + t] == 0) {
                //    printf("個人%d，時刻%dで", i, t);
                //    puts("入札確率が0です．");
                //}
//                printf("P[%d][%d] = %f\n", i, t, P[(Tmax + 1) * i + t]);
            } else {
                P[(Tmax + 1) * i + t] = 0;
            }
        }
    }
    
    return;
}

///*組み合わせの数を返す関数*/
//int combination(int n, int r)
//{
//    long long int deno1, deno2, frac;
//    int i;
//
//    if (r > n) {
//        printf("nCrのrの値が異常です．");
//        exit(0);
//    }
//
//    if (r == 0 || r == n) {
//        return 1;
//    }
//
//    frac = 1;
//    for (i = n; i >= 1; i--) {
//        frac *= i;
//    }
//
//    deno1 = 1;
//    for (i = n - r; i >= 1; i--) {
//        deno1 *= i;
//    }
//
//    deno2 = 1;
//    for (i = r; i >= 1; i--) {
//        deno2 *= i;
//    }
//
//    return (int)(frac / (deno1 * deno2));
//}

/*状態遷移確率の計算*/
void get_state_trans_prob(Network *link2, int n1, Demand *demand, int n2, Network *link, int n3, State *state, unsigned long long n4, Action *action, unsigned long long n5, double *p, double *P)
{
    unsigned long long i, j;
//    unsigned long long deno;
    int k, l, m;
    double sum = 0.0;
    int onum, dnum;
    unsigned short connection;
    unsigned short cond1, cond2, cond3, cond4, cond5, cond6, out, all_zero;

    for (i = 0; i < n5; i++) {
//        /*強制終了対策でスリープさせる*/
//        for (deno = 1; deno <= DENO; deno++) {
//            if (i == deno * n5 / DENO) {
//                sleep(5);
//            }
//        }
        
        if (action[i].presence) {
            sum = 0.0;
            
            grl_assignment(link2, n1, demand, n2, link, n3, action[i], P); //行動に対する入札確率を求める
            for (j = 0; j < n4; j++) {
                p[n4 * i + j] = 1;
                
                if (action[i].nowstate.t + 1 != state[j].t) {
                    p[n4 * i + j] = 0.0; //時間的に接続していない状態へは遷移しない
                    //puts("1"); //
                    continue;
                }
                
                connection = 1;
                for (k = 0; k < VNUMBER; k++) {
                    if (action[i].va[k].nextlink.id != state[j].vs[k].link.id) {
                        connection = 0;
                        break;
                    }
                }
                if (!connection) {
                    p[n4 * i + j] = 0.0; //遷移先のリンク以外へは遷移しない
                    //puts("2"); //
                    continue;
                }
                
                cond1 = 1;
                out = 0;
                for (k = 0; k < VNUMBER; k++) {
                    for (l = 0; l < n2; l++) {
                        if (action[i].va[k].x[l] == 1 && state[j].vs[k].sf[l] != 2) {
                            cond1 = 0;
                            out = 1;
                            break;
                        }
                    }
                    if (out) {
                        break;
                    }
                }
                if (!cond1) {
                    p[n4 * i + j] = 0.0;
                    //puts("3"); //
                    continue;
                }
                
                cond2 = 1;
                out = 0;
                for (k = 0; k < VNUMBER; k++) {
                    for (l = 0; l < n2; l++) {
                        if (action[i].nowstate.vs[k].sf[l] == 1 && action[i].va[k].x[l] == 0 && state[j].vs[k].sf[l] != 0) {
                            cond2 = 0;
                            out = 1;
                            break;
                        }
                    }
                    if (out) {
                        break;
                    }
                }
                if (!cond2) {
                    p[n4 * i + j] = 0.0;
                    //puts("4"); //
                    continue;
                }
                
                cond3 = 1;
                cond4 = 1;
                cond5 = 1;
                cond6 = 1;
                out = 0;
                for (k = 0; k < VNUMBER; k++) {
                    for (l = 0; l < n2; l++) {
                        onum = -1;
                        dnum = -1;
                        for (m = 0; m < n3; m++) {
                            if (link[m].id == (demand[l].o / 10) * 1000 + (demand[l].o % 10) * 10) {
                                onum = m;
                            }
                            if (link[m].id == (demand[l].d / 10) * 1000 + (demand[l].d % 10) * 10) {
                                dnum = m;
                            }
                        }
                        if (onum == -1 || dnum == -1) {
                            puts("onumまたはdnumが見つかりません．");
                            exit(EXIT_FAILURE);
                        }
                        
                        if (action[i].nowstate.vs[k].sf[l] == 2 && action[i].va[k].nextlink.o == link[onum].d && state[j].vs[k].sf[l] != 3) {
                            cond3 = 0;
                            out = 1;
                            //puts("5"); //
                            break;
                        }
                        if (action[i].nowstate.vs[k].sf[l] == 2 && action[i].va[k].nextlink.o != link[onum].d && state[j].vs[k].sf[l] != 2) {
                            cond4 = 0;
                            out = 1;
                            //puts("6"); //
                            break;
                        }
                        if (action[i].nowstate.vs[k].sf[l] == 3 && action[i].nowstate.vs[k].link.d == link[dnum].o && state[j].vs[k].sf[l] != 0) {
                            cond5 = 0;
                            out = 1;
                            //puts("7"); //
                            break;
                        }
                        if (action[i].nowstate.vs[k].sf[l] == 3 && action[i].nowstate.vs[k].link.d != link[dnum].o && state[j].vs[k].sf[l] != 3) {
                            cond6 = 0;
                            out = 1;
                            //puts("8"); //
                            break;
                        }
                    }
                    if (out) {
                        break;
                    }
                }
                if (!cond3 || !cond4 || !cond5 || !cond6) {
                    p[n4 * i + j] = 0.0;
                    continue;
                }
                
                out = 0;
                for (k = 0; k < n2; k++) {
                    for (l = 0; l < VNUMBER; l++) {
                        if (action[i].nowstate.vs[l].sf[k] == 0 && (state[j].vs[l].sf[k] == 2 || state[j].vs[l].sf[k] == 3)) {
                            p[n4 * i + j] = 0.0;
                            out = 1;
                            break;
                        }
                    }
                    if (out) {
                        break;
                    }
                    
                    if (state[j].vs[0].sf[k] == 1) { //この時点で(0,...,0)から(1,...,1)への遷移であることは確定する
                        p[n4 * i + j] *= P[(Tmax + 1) * k + state[j].t];
                    }

                    all_zero = 1;
                    for (l = 0; l < VNUMBER; l++) {
                        if (action[i].nowstate.vs[l].sf[k] != 0) {
                            all_zero = 0;
                            break;
                        }
                    }
                    
                    if (all_zero && state[j].vs[0].sf[k] == 0) {
                        p[n4 * i + j] *= (1 - P[(Tmax + 1) * k + state[j].t]);
                    }
                }
                if (out) {
                    continue;
                }
                //puts("a");
                
                sum += p[n4 * i + j];
            }
            //printf("行動%lluの状態遷移確率格納完了\n", i);
//            if ((int)sum != 1 && sum != 1.0) {
//                printf("行動%lluにおいて合計値が%fになっています\n", i, sum);
//                for (j = 0; j < n4; j++) {
//                    if (p[n4 * i + j] > 0) {
//                        printf("p[%llu][%llu] = %f\n", i, j, p[n4 * i + j]);
//                        printf("t = %d\n", state[j].t);
//                        for (k = 0; k < VNUMBER; k++) {
//                            printf("l_%d = %d\n", k, state[j].vs[k].link.id);
//                            for (l = 0; l < n2; l++) {
//                                printf("sf_%d%d = %u\n", k, l, state[j].vs[k].sf[l]);
//                            }
//                        }
//                    }
//                }
//            }
        }
    }
    
    return;
}

/*こっちはt=0にどの状態を取るかの確率を求めるために必要*/
void grl_assignment2(Network *link2, int n1, Demand *demand, int n2, Network *link, int n3, State state, double *P)
{
    int i, j, t;
    int num1; //デマンド交通リンクの本数
    int num2; //待ちリンクの本数
    int N; //link3の要素数
    int idmax = INT_MAX; //変えないこと
    int nidmax = INT_MAX;
    int onum, dnum;
    double tmp;
    Network link3[256];
    double pr[2048];

    for (i = 0; i < n2; i++) { //全ての需要についての繰り返し
        /*----------デマンド交通リンクと待ちリンクを追加してリンクデータを完成----------*/
        num1 = (int)(demand[i].e * (dijkstra((demand[i].o / 10) * 1000 + (demand[i].o % 10) * 10, (demand[i].d / 10) * 1000 + (demand[i].d % 10) * 10, link, n3) - 1));
        
        tmp = 0.0;
        for (j = 0; j < VNUMBER; j++) {
            tmp += demand[i].e * dijkstra(state.vs[j].link.id, (demand[i].o / 10) * 1000 + (demand[i].o % 10) * 10, link, n3);
        }
        tmp /= VNUMBER;
        if (tmp <= 1) {
            num2 = 1;
        } else {
            num2 = tmp - 1;
        }
        
        N = n1 + num1 + num2;
//        link3 = (Network *)realloc(link3, sizeof(Network) * N);
//        pr = (double * )realloc(pr, sizeof(double) * N * N * (Tmax + 1));
//        if (link3 == NULL || pr == NULL) {
//            puts("メモリ不足7");
//            exit(EXIT_FAILURE);
//        }

        onum = -1;
        dnum = -1;
        for (j = 0; j < n1; j++) {
            if (link2[j].id == demand[i].o) {
                onum = j;
            }
            if (link2[j].id == demand[i].d) {
                dnum = j;
            }
        }
        if (onum == -1 || dnum == -1) {
            puts("onumまたはdnumが見つかりません．");
            exit(EXIT_FAILURE);
        }

        /*デマンド交通リンク以外はlink2の複製で良い・ついでに即時効用の格納*/
        for (j = 0; j < n1; j++) {
            link3[j] = link2[j];
            for (t = 0; t <= Tmax; t++) {
                link3[j].v[t] = demand[i].beta_time * STEPTIME + demand[i].beta_fare * link3[j].f;
            }
            if (link3[j].o != link3[j].d) {
                link3[j].v[demand[i].tb - 1] = -DBL_MAX;
            }
        }
        
        /*デマンド交通のネットワーク*/
        link3[n1].id = idmax - num1 + 1;
        link3[n1].o = -nidmax;
        link3[n1].d = nidmax - num1 + 1;
        for (t = 0; t <= Tmax; t++) { //1本目
            link3[n1].v[t] = demand[i].beta_time * STEPTIME; //料金は先払いなので時間のみ
        }
        if (num1 == 1) {
            link3[n1].d = link3[dnum].o;
        }
        
        for (j = n1 + 1; j < n1 + num1; j++) { //2本目以降
            link3[j].id = link3[j - 1].id + 1;
            link3[j].o = link3[j - 1].d;
            if (j != n1 + num1 - 1) {
                link3[j].d = link3[j - 1].d + 1;
            } else {
                link3[j].d = link3[dnum].o;
            }
            
            for (t = 0; t < Tmax; t++) {
                link3[j].v[t] = demand[i].beta_time * STEPTIME; //料金は先払いなので時間のみ
            }
        }
        
        /*待ちリンク*/
        link3[n1 + num1].id = idmax - num1 - num2 + 1;
        link3[n1 + num1].o = link3[onum].d;
        link3[n1 + num1].d = nidmax - num1 - num2 + 1;
        for (t = 0; t < Tmax; t++) { //1本目
            if (t == demand[i].tb - 1) {
                link3[n1 + num1].v[t] = demand[i].beta_time * STEPTIME + demand[i].beta_fare * (F0 + F * num1) + demand[i].beta_exp; //料金は先払い・経験による信頼度も含めて判断
            } else {
                link3[n1 + num1].v[t] = -DBL_MAX;
            }
        }
        if (num2 == 1) {
            link3[n1 + num1].d = link3[n1].o;
        }
        
        for (j = n1 + num1 + 1; j < n1 + num1 + num2; j++) { //2本目以降
            link3[j].id = link3[j - 1].id + 1;
            link3[j].o = link3[j - 1].d;
            if (j != n1 + num1 + num2 - 1) {
                link3[j].d = link3[j - 1].d + 1;
            } else {
                link3[j].d = link3[n1].o;
            }
            
            for (t = 0; t < Tmax; t++) {
                link3[j].v[t] = demand[i].beta_time * STEPTIME; //料金は先払いなので時間のみ
            }
        }
        
        /*--------------------ここからgRLで配分--------------------*/
        /*指示関数の決定*/
        get_I(link3, N, demand[i]);

        /*期待最大効用を求める*/
        backward_induction_for_grl(link3, N, demand[i], num2);

        /*遷移確率行列を求める*/
        get_prob_matrix(link3, N, demand[i], pr);

        /*入札確率を格納*/
        for (t = 0; t <= Tmax; t++) {
            if (t == demand[i].tb - 1) {
                P[(Tmax + 1) * i + t] = pr[N * N * t + N * onum + n1 + num1];
                //printf("%f\n", P[(Tmax + 1) * i + t]);
                //if (P[(Tmax + 1) * i + t] == 0) {
                //    printf("個人%d，時刻%dで", i, t);
                //    puts("入札確率が0です．");
                //}
//                printf("P[%d][%d] = %f\n", i, t, P[(Tmax + 1) * i + t]);
            } else {
                P[(Tmax + 1) * i + t] = 0;
            }
        }
    }
    
    return;
}

/*最初の状態の確率*/
void first_state_prob(State *state, unsigned long long n1, double *first_p, unsigned long long n2, Network *link, int n3, Demand *demand, int n4, Network *link2, int n5, double *P)
{
    unsigned long long j, count;
    int k;
    double sum;
    
    count = 0;
    sum = 0.0;
    for (j = 0; j < n1; j++) {
        if (state[j].t == 0) {
            first_p[count] = 1.0 / (double)pow(n3, VNUMBER);
            grl_assignment2(link2, n5, demand, n4, link, n3, state[j], P);
            for (k = 0; k < n4; k++) {
                if (state[j].vs[0].sf[k] == 0) {
                    first_p[count] *= 1 - P[(Tmax + 1) * k];
                } else if (state[j].vs[0].sf[k] == 1) {
                    first_p[count] *= P[(Tmax + 1) * k];
                }
            }
            sum += first_p[count];
            count++;
        }
    }
    
    if (count != n2) {
        puts("初期状態の数が違います．");
        printf("count = %llu\n", count);
        printf("number_of_first_states = %llu\n", n2);
        exit(EXIT_FAILURE);
    }
    
    if (sum != 1.0) {
        printf("sum = %f\n", sum);
    }
    
    return;
}

/*後ろ向き帰納法*/
void backward_induction(State *state, Policy *pi, unsigned long long n1, Action *action, unsigned long long n2, double *p, double gamma)
{
    unsigned long long i, j, k;
    unsigned t;
    double tmp_max, ex_V;
    double max;
    unsigned long long opt_act;
    
    /*初期化*/
    for (i = 0; i < n1; i++) {
        state[i].V = 0.0;
    }
    t = Tmax;
    
    /*後ろ向き計算，終了判定*/
    while (t != 0) {
        t--;
        
//        printf("t = %u\n", t); //追加
        
        for (i = 0; i < n1; i++) {
            if (state[i].t == t) {
                max = -DBL_MAX;
                opt_act = -1;
                
                for (j = 0; j < n2; j++) {
                    if (action[j].nowstate.id == state[i].id) {
                        ex_V = 0;
                        for (k = 0; k < n1; k++) {
                            if (state[k].V < -DBL_MAX / 2) {
                                ex_V += p[n1 * j + k] * state[k].V; //こうすることで近視眼的に行動をとっても制約条件は守られる
                            } else {
                                ex_V += p[n1 * j + k] * gamma * state[k].V;
                            }
//                            printf("p = %f\n", p[n1 * j + k]);
//                            printf("state.V = %f\n", state[k].V);
//                            printf("ex_V = %f\n", ex_V); //追加
                        }
                        tmp_max = action[j].r + ex_V;
//                        if (i == 1231) {
//                            printf("action[%llu].r = %f\n", j, action[j].r);
//                            printf("ex_V = %f\n", ex_V);
//                            printf("tmp_max = %f\n", tmp_max); //追加
//                        }
                        
                        if (tmp_max > max) {
                            max = tmp_max;
                            opt_act = j;
                        }
                    }
                }
                if (opt_act == -1) {
//                    printf("状態%lluにおいて最適行動がありません．\n", i);
                    for (j = 0; j < n2; j++) {
                        if (action[j].nowstate.id == state[i].id) {
                            opt_act = j;
                            break;
                        }
                    }
                }
                
                state[i].V = max;
//                printf("state[%llu].V = %f\n", i, state[i].V); //追加
//                printf("pi[%llu].action.r = %f\n", i, pi[i].action.r); //追加
                pi[i].action = action[opt_act];
                pi[i].actionnum = opt_act;
            }
        }
//        putchar('\n'); //追加
    }
    
//    for (i = 0; i < n1; i++) {
//        if (state[i].t == 3) {
//            printf("pi[%llu].action.nowstate.t = %u\n", i, pi[i].action.nowstate.t); //追加
//        }
//    }
    
    return;
}

/*方策反復法*/
void policy_iteration(State *state, Policy *pi, unsigned long long n1, Action *action, unsigned long long n2, double *p, double gamma)
{
    unsigned long long i, j, k;
    int tmp_v;
    double delta = DBL_MAX;
    int stable;
    unsigned long long b;
    double max;
    unsigned long long argmax;
    double objective;
    unsigned count, count2;

    /*初期化*/
    for (i = 0; i < n1; i++) {
        pi[i].state = state[i]; //これは固定

        if (state[i].t == Tmax) {
            state[i].V = 0; //終端状態の状態価値関数は0
        } else {
            state[i].V = V_INITIAL;

            for (j = 0; j < n2; j++) {
                if (pi[i].state.id == action[j].nowstate.id) {
                    pi[i].action = action[j]; //1番最初の行動で初期化
                    pi[i].actionnum = j;
                }
            }
        }
    }

    count = 0;
    while (1) {
        count++;
        if (count % 10000 == 0) {
            printf("方策反復法繰り返し処理%u回目\n", count);
        }
        
        /*方策評価*/
        count2 = 0;
        while (delta >= MICRO) {
            count2++;
            if (count2 % 10000 == 0) {
                printf("方策評価%u-%u：", count, count2);
            }
            
            delta = 0;
            for (i = 0; i < n1; i++) {
                if (state[i].t != Tmax) {
                    tmp_v = state[i].V;

                    state[i].V = pi[i].action.r;
                    for (j = 0; j < n1; j++) {
                        if (state[j].V < -DBL_MAX / 2) {
                            state[i].V += p[n1 * pi[i].actionnum + j] * state[j].V; //こうすることで近視眼的に行動するときでも制約条件がかかる
                        } else {
                            state[i].V += p[n1 * pi[i].actionnum + j] * gamma * state[j].V;
                        }
                    }

                    delta = (delta > fabs(tmp_v - state[i].V)) ? delta : fabs(tmp_v - state[i].V);
                }
            }
            
            if (count2 % 10000 == 0) {
                printf("delta = %f\n", delta);
            }
        }

        /*方策改善*/
        stable = 1;
        for (i = 0; i < n1; i++) {
            if (state[i].t != Tmax) {
                b = pi[i].actionnum;

                max = -DBL_MAX;
                argmax = -1;
                for (j = 0; j < n2; j++) {
                    if (action[j].nowstate.id == state[i].id) {
                        objective = action[j].r;
                        for (k = 0; k < n1; k++) {
                            if (state[k].V < -DBL_MAX / 2) {
                                objective += p[n1 * j + k] * state[k].V;
                            } else {
                                objective += p[n1 * j + k] * gamma * state[k].V;
                            }
                        }

                        if (objective > max) {
                            max = objective;
                            argmax = j;
                        }
                    }
                }
                if (argmax == -1) {
                    //puts("方策改善：行き止まりの状態があります．");
                    continue;
                }
                pi[i].actionnum = argmax;
                pi[i].action = action[argmax];

                if (b != pi[i].actionnum) {
                    stable = 0;
                }
            }
        }

        if (stable) {
            break;
        }
    }
}

/*価値反復法*/
void value_iteration(State *state, Policy *pi, unsigned long long n1, Action *action, unsigned long long n2, double *p, double gamma)
{
    unsigned long long i, j, k;
    double delta = DBL_MAX;
    double tmp_v;
    double max, max2;
    double objective, objective2;
    unsigned long long argmax;
    unsigned count;

    for (i = 0; i < n1; i++) {
        state[i].V = 0;
        pi[i].state = state[i]; //固定
    }

    count = 0;
    while (delta >= MICRO) {
        count++;
        if (count % 10000 == 0) {
            printf("価値反復法繰り返し処理%u回目：", count);
        }
        
        delta = 0;

        for (i = 0; i < n1; i++) {
            if (state[i].t != Tmax) {
                tmp_v = state[i].V;

                max = -DBL_MAX;
                for (j = 0; j < n2; j++) {
                    if (action[j].nowstate.id == state[i].id) {
                        objective = action[j].r;
                        for (k = 0; k < n1; k++) {
                            if (state[k].V < -DBL_MAX / 2) {
                                objective +=  p[n1 * j + k] * state[k].V;
                            } else {
                                objective +=  p[n1 * j + k] * gamma * state[k].V;
                            }
                        }

                        if (objective > max) {
                            max = objective;
                        }
                    }
                }
                state[i].V = max;

                delta = (delta > fabs(tmp_v - state[i].V)) ? delta : fabs(tmp_v - state[i].V);
            }
        }
        if (count % 10000 == 0) {
            printf("delta = %f\n", delta);
        }
    }

    for (i = 0; i < n1; i++) {
        if (state[i].t != Tmax) {
            max2 = -DBL_MAX;
            argmax = -1;
            for (j = 0; j < n2; j++) {
                if (action[j].nowstate.id == state[i].id) {
                    objective2 = action[j].r;
                    for (k = 0; k < n1; k++) {
                        if (state[k].V < -DBL_MAX / 2) {
                            objective2 += p[n1 * j + k] * state[k].V;
                        } else {
                            objective2 += p[n1 * j + k] * gamma * state[k].V;
                        }
                    }

                    if (objective2 > max2) {
                        max2 = objective2;
                        argmax = j;
                    }
                }
            }
            if (argmax == -1) {
                //puts("価値反復：行き止まりの状態があります．");
                for (j = 0; j < n2; j++) {
                    if (state[i].id == action[j].nowstate.id) {
                        pi[i].actionnum = j;
                        pi[i].action = action[j];
                    }
                }
            }

            pi[i].actionnum = argmax;
            pi[i].action = action[argmax];
        }
    }
}

///*二項分布乱数を返す関数*/
//int bnldev(double pp, int n)
//{
//    double ran1;
//    int j;
//    double p, bnl;
//    int randmax = RAND_MAX;
//
//    p = (pp <= 0.5) ? pp : 1.0 - pp;
//
//    bnl = 0.0;
//    for (j = 1; j <= n; j++) {
//        ran1 = (double)rand() / (double)randmax;
//        if (ran1 < p) {
//            ++bnl;
//        }
//    }
//    if (p != pp) {
//        bnl = n - bnl;
//    }
//
//    return (int)bnl;
//}

///*確率に従った0-1乱数を返す関数*/
//int pdev(double pp)
//{
//    int bnl;
//
//    if ((double)rand() / (double)RAND_MAX < pp) {
//        bnl = 1;
//    } else {
//        bnl = 0;
//    }
//
//    return bnl;
//}



/*確率に従ってランダムに次の状態を返す関数*/
unsigned long long nextstate(unsigned long long actionnum, double *p, unsigned long long n) { //nはstateの数
    unsigned long long i;
    double random;

    random = (double)rand() / RAND_MAX;

    for (i = 0; i < n; i++) {
        random -= p[n * actionnum + i];
        if (random <= 0) {
            return i;
        }
    }
    
//    for (i = n - 1; i >= 0; i--) {
//        if (p[n * actionnum + i] > 0.0000) {
//            return i;
//        }
//    }

    puts("statenumが見つかりませんでした．");
    exit(EXIT_FAILURE);
}

/*確率に従ってランダムに最初の状態を返す関数*/
unsigned long long firststate(double *first_p, unsigned long long n1, State *state, unsigned long long n2)
{
    unsigned long long i, j, count;
    double random;

    random = (double)rand() / RAND_MAX;
    for (i = 0; i < 1 + (int)(rand() * (100 - 1 + 1.0) / (1.0 + RAND_MAX) ); i++) {
        random = (double)rand() / RAND_MAX;
    }

    for (i = 0; i < n1; i++) {
        random -= first_p[i];
        if (random <= 0) {
            count = 0;
            for (j = 0; j < n2; j++) {
                if (state[j].t == 0) {
                    if (count == i) {
                        return j;
                    }
                    count++;
                }
            }
        }
    }

    puts("初期状態が見つかりませんでした．");
    exit(EXIT_FAILURE);
    
//    for (j = n2 - 1; j >= 0; j--) {
//        if (state[j].t == 0) {
//            return j;
//        }
//    }
//
//    puts("初期状態が見つかりませんでした．");
//    exit(EXIT_FAILURE);
}

/*シミュレーション*/
double simulation(Policy *pi, Action *actionlist, State *statelist, State *state, unsigned long long n4, Demand *demand, int n5, Network *link2, int n6, Network *link, int n7, double *P, char *out_simulation, double *p, Action *action, unsigned long long n8, double *first_p, unsigned long long n9)
{
    int t;
    unsigned long long i;
    int j, k;
    unsigned long long statenum, actionnum;
//    unsigned short sf[n5];
//    int corres, out;
    FILE *fp;
    double G; //収益
    
    /*初期状態を作成*/
    t = 0;
    statenum = firststate(first_p, n9, state, n4);
    statelist[t] = state[statenum];
    G = 0.0;

    /*繰り返し処理*/
    while (t != Tmax) {
        actionlist[t] = pi[statenum].action; //行動を決定
        G += pi[statenum].action.r; //収益に追加
        
        actionnum = -1;
        for (i = 0; i < n8; i++) {
            if (actionlist[t].id == action[i].id) {
                actionnum = i;
            }
        }
        if (actionnum == -1) {
            puts("actionnumが見つかりませんでした．");
            exit(EXIT_FAILURE);
        }
        
        t++;
        statenum = nextstate(actionnum, p, n4);
        statelist[t] = state[statenum];
        //grl_assignment(link2, n6, demand, n5, link, n7, actionlist[t - 1], P, d, Q, link3, pr);
        //for (k = 0; k < n5; k++) {
        //    printf("%f\n", P[(Tmax + 1) * k + t]);
        //    sf[k] = pdev(P[(Tmax + 1) * k + t]);
        //}
//        statenum = -1;
//        for (i = 0; i < n4; i++) {
//            corres = 1;
//            if (p[n4 * actionnum + i] == 0) {
//                corres = 0;
//            } else {
//                out = 0;
//                for (k = 0; k < n5; k++) {
//                    for (j = 0; j < VNUMBER; j++) {
//                        if (state[i].vs[j].sf[k] != sf[k]) {
//                            corres = 0;
//                            out = 1;
//                            break;
//                        }
//                    }
//                    if (out) {
//                        break;
//                    }
//                }
//            }
//
//            if (corres) {
//                statelist[t] = state[i];
//                statenum = i;
//                break;
//            }
//        }
//        if (statenum == -1) {
//            puts("statenumが見つかりませんでした．");
//            exit(EXIT_FAILURE);
//        }
        
//        printf("t = %d\n", t);
//        printf("状態：%llu\n", statelist[t].id);
    }
    
    if (RESULT_OUT) {
        /*ファイルへの書き出し*/
        fp = fopen(out_simulation, "w");
        if (fp == NULL) {
            printf("ファイル名%sが開けません．\n", out_simulation);
            exit(EXIT_FAILURE);
        }
        
        /*1行目*/
        fprintf(fp, "t,");
        for (j = 0; j < VNUMBER - 1; j++) {
            fprintf(fp, "l_%dt,", j);
            for (k = 0; k < n5; k++) {
                fprintf(fp, "sf_%d%dt,", j, k);
            }
        }
        fprintf(fp, "l_%dt,", VNUMBER - 1);
        for (k = 0; k < n5 - 1; k++) {
            fprintf(fp, "sf_%d%dt,", VNUMBER - 1, k);
        }
        fprintf(fp, "sf_%d%dt\n", VNUMBER - 1, n5 - 1);
        
        /*2行目以降*/
        for (t = 0; t <= Tmax; t++) {
            fprintf(fp, "%u,", statelist[t].t);
            for (j = 0; j < VNUMBER - 1; j++) {
                fprintf(fp, "%d,", statelist[t].vs[j].link.id);
                for (k = 0; k < n5; k++) {
                    fprintf(fp, "%u,", statelist[t].vs[j].sf[k]);
                }
            }
            fprintf(fp, "%d,", statelist[t].vs[VNUMBER - 1].link.id);
            for (k = 0; k < n5 - 1; k++) {
                fprintf(fp, "%u,", statelist[t].vs[VNUMBER - 1].sf[k]);
            }
            fprintf(fp, "%u\n", statelist[t].vs[VNUMBER - 1].sf[n5 - 1]);
        }
        fclose(fp);
    }
    
    return G; //収益を返す
}

int main(void)
{
    /*時間計測用変数用意，時間計測開始*/
    clock_t start, step1, step2, step3, step4, step5, step6, step7, step8, end;
    start = clock();
    
    /*擬似乱数の種用意*/
    srand((unsigned)time(NULL));

    /*--------------------変数の準備--------------------*/

    /*dijkstra関数内で用いる*/
//    int *d = NULL, *Q = NULL;
//    int *prev; //前にdijkstraを呼び出したときのn
//    prev = (int *)malloc(sizeof(int));
//    *prev = -1; //-1で初期化しておく
    
    /**/
//    Network *link3 = NULL;
//    double *pr = NULL;
    
    /*デマンド交通のリンク数カウント用*/
    int number_of_links;

    /*インプットファイル名*/
    char *in_network = "/Users/taikisuzuki/Desktop/graduation_thesis/numerical_results/18/demandlink_18.csv"; //デマンド交通のネットワークデータ
    char *in_od = "/Users/taikisuzuki/Desktop/graduation_thesis/numerical_results/18/OD_matrix_18_1_30.csv"; //時間制約付きOD表
    char *in_network2 = "/Users/taikisuzuki/Desktop/graduation_thesis/numerical_results/18/non_demandlink_18.csv"; //需要側のネットワークデータ
    
    /*アウトプットファイル名*/
    char *out_simulation[] = {
        "/home/suzuki/graduation_thesis/numerical_results/14/result_14_7_30_0.csv",
        "/home/suzuki/graduation_thesis/numerical_results/14/result_14_7_30_0.5.csv",
        "/home/suzuki/graduation_thesis/numerical_results/14/result_14_7_30_1.csv"
    };
    char *out_revenue[] = {
        "/home/suzuki/graduation_thesis/numerical_results/14/revenue_14_test3_0.csv",
        "/home/suzuki/graduation_thesis/numerical_results/14/revenue_14_test3_0.5.csv",
        "/Users/taikisuzuki/Desktop/graduation_thesis/numerical_results/18/revenue_18_1_30.csv"
    };

    /*デマンド交通のネットワークデータ仮格納用*/
    Network *linklist = NULL;

    /*デマンド交通のネットワークデータ格納用（リンク数は変数なので，動的配列を使う）*/
    Network *link;

    /*OD表カウント用*/
    int number_of_od;

    /*OD表仮格納用*/
    Demand *odlist = NULL;

    /*OD表格納用（リンク数は変数なので，動的配列を使う）*/
    Demand *demand;

    /*状態数*/
    unsigned long long number_of_states;

    /*状態格納用*/
    State *state;

    /*行動数*/
    unsigned long long number_of_actions;

    /*行動格納用*/
    Action *action;

    /*需要側リンク数カウント用*/
    int number_of_links2;

    /*需要側のネットワークデータ仮格納用*/
    Network *linklist2 = NULL;

    /*需要側のネットワークデータ格納用（リンク数は変数なので，動的配列を使う）*/
    Network *link2;

    /*入札確率*/
    double *P;

    /*状態遷移確率*/
    double *p;
    
    /*時間割引率*/
    double gamma[] = {gamma_a, gamma_b, gamma_c};

    /*最適方策*/
    Policy *pi;

    /*行動列（シミュレーション）*/
    Action *actionlist;

    /*状態列（シミュレーション）*/
    State *statelist;
    
    /*最初の状態の確率*/
    double *first_p = NULL;
    
    /*初期状態数*/
    unsigned long long number_of_first_states;

    unsigned long long i;
    int j, t, k;
    FILE *fp_main;
    double revenue;

    /*--------------------ここから実際の処理--------------------*/

    /*デマンド交通のネットワーク仮格納（リンク数の数え上げ）*/
    linklist = input_network(linklist, in_network, &number_of_links);

    /*デマンド交通のネットワークデータ格納用の配列の確保*/
    link = (Network *)malloc(sizeof(Network) * number_of_links);
    if (link == NULL) {
        puts("メモリ不足8");
        exit(EXIT_FAILURE);
    }

    /*デマンド交通のネットワークデータ格納*/
    set_network(link, linklist, in_network, number_of_links);
    step1 = clock();
    printf("経過時間：%f[s]\n\n", (double)(step1 - start) / CLOCKS_PER_SEC);

    /*OD表の仮格納（数え上げ）*/
    odlist = input_demand(odlist, in_od, &number_of_od);

    /*OD表格納用の配列の確保*/
    demand = (Demand *)malloc(sizeof(Demand) * number_of_od);
    if (demand == NULL) {
        puts("メモリ不足9");
        exit(EXIT_FAILURE);
    }

    /*OD表格納*/
    set_demand(demand, odlist, in_od, number_of_od);
    step2 = clock();
    printf("経過時間：%f[s]\n\n", (double)(step2 - start) / CLOCKS_PER_SEC);

    /*状態数の計算*/
    number_of_states = how_many_states(demand, link, number_of_od, number_of_links);

    /*状態格納用の配列の確保*/
    state = (State *)malloc(sizeof(State) * number_of_states);
    if (state == NULL) {
        puts("メモリ不足10");
        exit(EXIT_FAILURE);
    }

    /*状態の格納，最終状態数・行動数計算*/
    set_states(state, number_of_states, demand, number_of_od, link, number_of_links);
    number_of_actions = how_many_actions(link, number_of_links, state, number_of_states, demand, number_of_od);
    printf("状態と行動との組み合わせ数：%llu\n", number_of_actions);
    step3 = clock();
    printf("経過時間：%f[s]\n\n", (double)(step3 - start) / CLOCKS_PER_SEC);

    /*行動格納用の配列の確保*/
    action = (Action *)malloc(sizeof(Action) * number_of_actions);
    if (action == NULL) {
        puts("メモリ不足11");
        exit(EXIT_FAILURE);
    }

    /*行動の格納*/
    set_action(action, number_of_actions, link, number_of_links, state, number_of_states, demand, number_of_od);
    step4 = clock();
    printf("経過時間：%f[s]\n\n", (double)(step4 - start) / CLOCKS_PER_SEC);

    /*需要側のネットワーク仮格納（リンク数の数え上げ）*/
    linklist2 = input_network2(linklist2, in_network2, &number_of_links2);

    /*需要側のネットワークデータ格納用の配列の確保*/
    link2 = (Network *)malloc(sizeof(Network) * (number_of_links2));
    if (link2 == NULL) {
        puts("メモリ不足12");
        exit(EXIT_FAILURE);
    }

    /*需要側のネットワークデータ格納*/
    set_network2(link2, linklist2, in_network2, number_of_links2);
    step5 = clock();
    printf("経過時間：%f[s]\n\n", (double)(step5 - start) / CLOCKS_PER_SEC);


    /*入札確率の配列の確保*/
    P = (double *)malloc(sizeof(double) * (number_of_od) * (Tmax + 1));
    if (P == NULL) {
        puts("メモリ不足13");
        exit(EXIT_FAILURE);
    }

    /*状態遷移確率の配列の確保*/
    p = (double *)malloc(sizeof(double) * (number_of_states) * (number_of_actions));

    /*状態遷移確率の計算*/
    get_state_trans_prob(link2, number_of_links2, demand, number_of_od, link, number_of_links, state, number_of_states, action, number_of_actions, p, P);
    puts("状態遷移確率計算完了");
    step6 = clock();
    printf("経過時間：%f[s]\n\n", (double)(step6 - start) / CLOCKS_PER_SEC);
    
    /*first_pのメモリ確保*/
    number_of_first_states = 0;
    for (i = 0; i < number_of_states; i++) {
        if (state[i].t == 0) {
            number_of_first_states++;
        }
    }
    first_p = (double *)malloc(sizeof(double) * number_of_first_states);
    if (first_p == NULL) {
        puts("first_pのメモリ確保失敗");
        exit(EXIT_FAILURE);
    }
    
    /*最初の状態の確率を計算*/
    first_state_prob(state, number_of_states, first_p, number_of_first_states, link, number_of_links, demand, number_of_od, link2, number_of_links2, P);

    /*最適方策の配列の確保*/
    pi = (Policy *)malloc(sizeof(Policy) * number_of_states);
    if (pi == NULL) {
        puts("メモリ不足14");
        exit(EXIT_FAILURE);
    }

    /*状態列と行動列の配列を確保*/
    actionlist = (Action *)malloc(sizeof(Action) * Tmax);
    statelist = (State *)malloc(sizeof(State) * (Tmax + 1));
    if (actionlist == NULL || statelist == NULL) {
        puts("メモリ不足15");
        exit(EXIT_FAILURE);
    }
    for (t = 0; t < Tmax; t++) {
        actionlist[t].va = (V_Action *)malloc(sizeof(V_Action) * VNUMBER);
        if (actionlist[t].va == NULL) {
            puts("メモリ確保失敗16");
            exit(EXIT_FAILURE);
        }
        for (j = 0; j < VNUMBER; j++) {
            actionlist[t].va[j].x = (unsigned short *)malloc(sizeof(unsigned short) * number_of_od);
            if (actionlist[t].va[j].x == NULL) {
                puts("メモリ確保失敗17");
                exit(EXIT_FAILURE);
            }
        }
    }
    for (t = 0; t <= Tmax; t++) {
        statelist[t].vs = (V_State *)malloc(sizeof(V_State) * VNUMBER);
        if (statelist[t].vs == NULL) {
            puts("メモリ確保失敗18");
            exit(EXIT_FAILURE);
        }
        for (j = 0; j < VNUMBER; j++) {
            statelist[t].vs[j].sf = (unsigned short *)malloc(sizeof(unsigned short) * number_of_od);
            if (statelist[t].vs[j].sf == NULL) {
                puts("メモリ確保失敗19");
                exit(EXIT_FAILURE);
            }
        }
    }
    
    /*ケースごとの計算*/
    for (j = 2; j < 3; j++) {
        printf("ケース%dの計算開始\n\n", j);
        
        /*最適化*/
        if (SOLUTION == 0) {
            backward_induction(state, pi, number_of_states, action, number_of_actions, p, gamma[j]);
            printf("後ろ向き帰納法で");
        } else if (SOLUTION == 1) {
            policy_iteration(state, pi, number_of_states, action, number_of_actions, p, gamma[j]);
            printf("方策反復法で");
        } else {
            value_iteration(state, pi, number_of_states, action, number_of_actions, p, gamma[j]);
            printf("価値反復法で");
        }
        puts("最適化完了");
        step7 = clock();
        printf("経過時間：%f[s]\n\n", (double)(step7 - start) / CLOCKS_PER_SEC);
        
        /*シミュレーション*/
        fp_main = fopen(out_revenue[j], "w");
        if (fp_main == NULL) {
            printf("ファイル%sが開けません．\n", out_revenue[j]);
            exit(EXIT_FAILURE);
        }
        
        fprintf(fp_main, "number,revenue\n"); //1行目
        
        for (k = 0; k < TRIALS; k++) {
            revenue = simulation(pi, actionlist, statelist, state, number_of_states, demand, number_of_od, link2, number_of_links2, link, number_of_links, P, out_simulation[j], p, action, number_of_actions, first_p, number_of_first_states);
            
            fprintf(fp_main, "%d,%f\n", k + 1, revenue);
        }
        
        fclose(fp_main);
        
        printf("ケース%dの計算終了\n\n", j);
        step8 = clock();
        printf("経過時間：%f[s]\n\n", (double)(step8 - start) / CLOCKS_PER_SEC);
    }

    /*メモリの解放*/
//    free(d);
//    free(Q);
//    free(prev);
//    free(link3);
//    free(pr);
    free(link);
    free(demand);
    for (i = 0; i < number_of_states; i++) {
        for (j = 0; j < VNUMBER; j++) {
            free(state[i].vs[j].sf);
        }
        free(state[i].vs);
    }
    free(state);
    for (i = 0; i < number_of_actions; i++) {
        for (j = 0; j < VNUMBER; j++) {
            free(action[i].va[j].x);
        }
        free(action[i].va);
    }
    free(action);
    free(link2);
    free(p);
    free(P);
    free(pi);
    free(actionlist);
    free(statelist);
    free(first_p);

    /*全計算時間記録*/
    puts("全計算終了");
    end = clock();
    printf("経過時間：%f[s]\n\n", (double)(end - start) / CLOCKS_PER_SEC);

    return 0;
}

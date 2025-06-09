#include<stdio.h>
#include<string.h>
#include<stdlib.h>
#include<math.h>
typedef int I;typedef void V,*U;typedef char C;typedef double F;
#define pf printf
#define Z static
#define R return
#define Rm R m
#define RQ R QQ
#define Rt R Sm("#t")
#define $(b,a...) if(b){a;}else
#define $$(b,a...) if(b){a;}
#define _(z) ({z;})
#define W(z) while(_(z))
I digit(I c){R (c<='9')&&(c>='0');} //ctype.h
I space(I c){R c==' '||c=='\f'||c=='\n'||c=='\r'||c=='\t'||c=='\v';}
#define i(a...) for(a;!isNil(xs);xs=cdr(xs))
#define Tx T(x)
#define Tv T(v)
#define Fx F x
#define Ux U x
#define Uy U y
#define Uz U z
#define U1(m,a...) U m(Ux){a;}
#define U2(m,a...) U m(Ux,Uy){a;}
#define U3(m,a...) U m(Ux,Uy,Uz){a;}
#define Qnum pf("expect num\n");RQ
#define Qarg pf("expect arg\n");RQ
#define Qpair pf("expect pair\n");RQ
#define Qcl pf("bad clause\n");RQ
#define Qcnd pf("cond: else must be the last\n");RQ
#define Qldn pf("load: expect filename\n");RQ
#define Qlds pf("load: filename must be symbol\n");RQ
#define Qmac pf("bad macro syntax\n");RQ
#define Qfun pf("expect function\n");RQ
extern U rexpr(V);
extern V rdt(V);
extern U eval(Ux,Uy);
I Num=1,Sym=2,Pair=3,Nil=4,Clos=5;
Z FILE *IF=NULL;U nil,genv,macenv,QQ; //slient
C token[128];I ready=0;
I T(Ux){R*(I*)x;} //type
U Nm(Fx){C*m=malloc(12);*(I*)m=Num;*(F*)(m+sizeof(I))=x;Rm;}
F gNm(Ux){R*(F*)((C*)x+sizeof(I));}
U Sm(C*s){I l=strlen(s)+1;C*m=malloc(sizeof(I)+l);*(I*)m=Sym;memcpy(m+sizeof(I),s,l);Rm;}
C*gSm(Ux){R(C*)x+sizeof(I);}
U1(car,R((U*)x)[1])U1(cdr,R((U*)x)[2])
U2(cons,U*m=malloc(3*sizeof(U));*(I*)m=Pair;m[1]=x;m[2]=y;Rm)
U3(closure,C*m=malloc(sizeof(I)+3*sizeof(U));*(I*)m=Clos;U*f=(U*)(m+sizeof(I));f[0]=x;f[1]=y;f[2]=z;Rm) //tg+param+body+env
I eq(Ux,Uy){$$(T(x)!=T(y),R 0)$$(Tx==Sym,R!strcmp(gSm(x),gSm(y)))$$(Tx==Num,R gNm(x)==gNm(y))R x==y;}
U1(clop,R((U*)((C*)x+sizeof(I)))[0])
U1(clob,R((U*)((C*)x+sizeof(I)))[1])
U1(cloe,R((U*)((C*)x+sizeof(I)))[2])
I isNil(Ux){R x==nil||Tx==Nil;}
I isAtom(Ux){R Tx==Sym||Tx==Num||isNil(x);}
V pt(Ux){$$(x==QQ,return)$(isNil(x),pf("#nil"))
$(Tx==Num,F v=gNm(x),ip;$(modf(v,&ip)==0.0&&fabs(v)<9e15,pf("%.0f",v)){pf("%g",v);})
$$(Tx==Sym,pf("%s",gSm(x)))$$(Tx==Pair,pf("(");W(Tx==Pair){pt(car(x));x=cdr(x);$$(Tx==Pair,pf(" "))}$$(!isNil(x),pf(" . ");pt(x))pf(")");)}
U2(f_add,F s=0;i(U xs=x){U v=eval(car(xs),y);$$(Tv!=Num,Qnum)s+=gNm(v);}R Nm(s))
U2(f_mul,F p=1;i(U xs=x){U v=eval(car(xs),y);$$(Tv!=Num,Qnum)p*=gNm(v);}R Nm(p))
U2(f_minus,$$(isNil(x),Qarg)U a1=eval(car(x),y);$$(T(a1)!=Num,Qnum)F r=gNm(a1);
x=cdr(x);$$(isNil(x),R Nm(-r))i(U xs=x){U v=eval(car(xs),y);$$(Tv!=Num,Qnum)r-=gNm(v);}R Nm(r);)
U2(f_div,$$(isNil(x),Qarg)U a1=eval(car(x),y);$$(T(a1)!=Num,Qnum)F r=gNm(a1);
x=cdr(x);$$(isNil(x),R Nm(1.0/r))i(U xs=x){U v=eval(car(xs),y);$$(Tv!=Num,Qnum)r/=gNm(v);}R Nm(r))
U2(f_sqrt,$$(!isNil(cdr(x)),Qarg;)U v=eval(car(x),y);$$(Tv!=Num,Qnum)R Nm(sqrt(gNm(v))))
U2(f_quote,(V)y;R car(x))
U2(f_atom,R isAtom(eval(car(x),y))?Sm("#t"):nil)
U2(f_eq,U a=eval(car(x),y),b=eval(car(cdr(x)),y); R eq(a,b)?Sm("#t"):nil)
U2(f_lt,U f=eval(car(x),y);$$(T(f)!=Num,Qnum)i(U xs=cdr(x)){U nxt=eval(car(xs),y);
$$(T(nxt)!=Num,Qnum)$$(!(gNm(f)<gNm(nxt)),R nil)f=nxt;}Rt;)
U2(f_gt,U f=eval(car(x),y);$$(T(f)!=Num,Qnum)i(U xs=cdr(x)){U nxt=eval(car(xs),y);
$$(T(nxt)!=Num,Qnum)$$(!(gNm(f)>gNm(nxt)),R nil)f=nxt;}Rt;)
U2(f_car,$$(isNil(x),Qarg)U v=eval(car(x),y);$$(Tv!=Pair,Qpair)R car(v);)
U2(f_cdr,$$(isNil(x),Qarg)U v=eval(car(x),y);$$(Tv!=Pair,Qpair)R cdr(v);)
U2(f_cons,R cons(eval(car(x),y),eval(car(cdr(x)),y)))
U2(f_and,$$(isNil(x),Rt)i(U xs=x){U v=eval(car(xs),y);$$(isNil(v),R nil)}Rt;)
U2(f_or,$$(isNil(x),R nil)i(U xs=x){U v=eval(car(xs),y);$$(!isNil(v),Rt)}R nil;)
U2(f_xor,I cnt=0;i(U xs=x){U v=eval(car(xs),y);$$(!isNil(v),cnt++)}R(cnt%2)?Sm("#t"):nil;)
U2(f_not,$$(isNil(x)||!isNil(cdr(x)),Qarg)U v=eval(car(x),y);R isNil(v)?Sm("#t"):nil;)
U2(f_define,U f=car(x);$(T(f)==Sym,U ph=cons(f,nil);genv=cons(ph,genv);U val=eval(car(cdr(x)),genv);
((U*)ph)[2]=val;R f){U m=car(f),p=cdr(f),body=car(cdr(x));U ph=cons(m,nil);genv=cons(ph,genv);
U clo=closure(p,body,genv);((U*)ph)[2]=clo;Rm;})
U2(f_lambda,R closure(car(x),car(cdr(x)),y))
U2(f_if,U c=eval(car(x),y);$(!isNil(c),R eval(car(cdr(x)),y)){R eval(car(cdr(cdr(x))),y);})
U2(f_cond,i(U xs=x){U ps=car(xs);$$(isNil(ps)||isNil(cdr(ps)),Qcl)U t=car(ps),b=cdr(ps);
$(T(t)==Sym&&!strcmp(gSm(t),"else"),$$(!isNil(cdr(xs)),Qcnd))
{U res=eval(t,y);$$(isNil(res),continue)}U m=nil;i(U xs=b){m=eval(car(xs),y);}Rm;}R nil;)
U2(f_macro,$$(isNil(x)||isNil(cdr(x))||isNil(cdr(cdr(x))),Qmac)
U m=car(x),rst=cdr(x),p=car(rst),bdy=car(cdr(rst)),tmp=closure(p,bdy,y);macenv=cons(cons(m,tmp),macenv);R m;)
U2(f_load,$$(isNil(x),Qldn)U fn=eval(car(x),y);$$(T(fn)!=Sym,Qlds)
FILE *oldIF=IF;IF=fopen(gSm(fn),"r");$$(!IF,perror(gSm(fn));IF=oldIF;R QQ)ready=0;
W(1){rdt();$$(IF == stdin,break)U expr=rexpr();eval(expr,genv);ready=0;}IF=oldIF;ready=0;RQ;)

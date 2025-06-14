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
#define Rt R tr
#define $(b,a...) if(b){a;}else
#define $$(b,a...) if(b){a;}
#define _(z) ({z;})
#define W(z) while(_(z))
I digit(I c){R (c<='9')&&(c>='0');} //ctype.h
I space(I c){R c==' '||c=='\f'||c=='\n'||c=='\r'||c=='\t'||c=='\v';}
#define i(a...) for(a;!isNil(xs);xs=cdr(xs))
#define i2(a...) for(a;!isNil(ps);ps=cdr(ps))
#define Tx T(x)
#define Ty T(y)
#define Tv T(v)
#define Tf T(f)
#define Fx F x
#define Ux U x
#define Uy U y
#define Uz U z
#define Uf U f=eval(car(xs),y)
#define Uv U v=eval(car(x),y)
#define U1(m,a...) U m(Ux){a;}
#define U2(m,a...) U m(Ux,Uy){a;}
#define U3(m,a...) U m(Ux,Uy,Uz){a;}
#define Qcl pf("bad clause\n");RQ
#define Qsh pf("shape mismatch\n");RQ
#define Qnum pf("expect num\n");RQ
#define Qarg pf("expect arg\n");RQ
#define Qcnd pf("cond: else must be the last\n");RQ
#define Qldn pf("load: expect filename\n");RQ
#define Qlds pf("load: filename must be symbol\n");RQ
#define Qmac pf("bad macro syntax\n");RQ
#define Qfun pf("expect function\n");RQ
#define Qpair pf("expect pair\n");RQ
#define P(a,b,c) $$(T(a)!=b,c) //panic early
#define man "  +  -  *  /  %%  sqrt  quote  atom  eq  car  cdr  cons  list  define  lambda\n  if  <  >  cond  and  or  xor  not  load  defmacro\n"
U rexpr(V);V rdt(V);U eval(Ux,Uy);U bc2(Ux,Uy,U(*op)(U,U));U bc1(Ux,U(*op)(U));
I Num=1,Sym=2,Pair=3,Nil=4,Clos=5,True=6;
Z FILE *IF=NULL;U nil,tr,genv,macenv,QQ; //slient
C token[128];I ready=0;
I T(Ux){R*(I*)x;} //type
U Nm(Fx){C*m=malloc(12);*(I*)m=Num;*(F*)(m+sizeof(I))=x;Rm;}
F gNm(Ux){R*(F*)((C*)x+sizeof(I));}
U Sm(C*s){I l=strlen(s)+1;C*m=malloc(sizeof(I)+l);*(I*)m=Sym;memcpy(m+sizeof(I),s,l);Rm;}
C*gSm(Ux){R(C*)x+sizeof(I);}
U1(car,R((U*)x)[1])U1(cdr,R((U*)x)[2])
U2(cons,U*m=malloc(3*sizeof(U));*(I*)m=Pair;m[1]=x;m[2]=y;Rm)
U3(closure,C*m=malloc(sizeof(I)+3*sizeof(U));*(I*)m=Clos;U*f=(U*)(m+sizeof(I));f[0]=x;f[1]=y;f[2]=z;Rm) //tg+param+body+env
U1(clop,R((U*)((C*)x+sizeof(I)))[0])U1(clob,R((U*)((C*)x+sizeof(I)))[1])U1(cloe,R((U*)((C*)x+sizeof(I)))[2])
I eq(Ux,Uy){$$(T(x)!=T(y),R 0)$$(Tx==Sym,R!strcmp(gSm(x),gSm(y)))$$(Tx==Num,R gNm(x)==gNm(y))$$(Tx==Pair,R eq(car(x),car(y))&&eq(cdr(x),cdr(y));)R x==y;}
I isNil(Ux){R x==nil||Tx==Nil;}I isAtom(Ux){R Tx==Sym||Tx==Num||isNil(x)||Tx==True;}
V pt(Ux){$$(x==QQ,R)$$(isNil(x),pf("#nil");R)$$(Tx==True,pf("#t");R)
$$(Tx==Num,F v=gNm(x),ip;$(modf(v,&ip)==0.0&&fabs(v)<9e15,pf("%.0f",v)){pf("%g",v);})
$$(Tx==Sym,pf("%s",gSm(x)))$$(Tx==Pair,pf("(");W(Tx==Pair){pt(car(x));x=cdr(x);$$(Tx==Pair,pf(" "))}$$(!isNil(x),pf(" . ");pt(x))pf(")");)}
U add(Ux,Uy){R Nm(gNm(x)+gNm(y));}
U mul(Ux,Uy){R Nm(gNm(x)*gNm(y));}
U sub(Ux,Uy){R Nm(gNm(x)-gNm(y));}
U _div(Ux,Uy){R Nm(gNm(x)/gNm(y));}
U _sqrt(Ux){R Nm(sqrt(gNm(x)));}
U _mod(Ux,Uy){R Nm(fmod(gNm(x),gNm(y)));}
U2(f_add,$$(isNil(x),R Nm(0))Uv;i(U xs=cdr(x)){Uf;v=bc2(v,f,add);$$(v==QQ,RQ)}R v;)
U2(f_mul,$$(isNil(x),R Nm(1))Uv;i(U xs=cdr(x)){Uf;v=bc2(v,f,mul);$$(v==QQ,RQ)}R v;)
U2(f_minus,$$(isNil(x),Qarg)U a=eval(car(x),y);$$(isNil(cdr(x)),P(a,Num,Qnum);R Nm(-gNm(a)))U b=eval(car(cdr(x)),y);
$$(T(a)==Pair||T(b)==Pair,R bc2(a,b,sub))P(a,Num,Qnum)F r=gNm(a);x=cdr(x);i(U xs=x)
{U v=eval(car(xs),y);P(v,Num,Qnum)r-=gNm(v);}R Nm(r);)
U2(f_div,$$(isNil(x),Qarg)U a=eval(car(x),y);$$(isNil(cdr(x)),P(a,Num,Qnum);R Nm(1.0/gNm(a)))U b=eval(car(cdr(x)),y);
$$(T(a)==Pair||T(b)==Pair,R bc2(a,b,_div))P(a,Num,Qnum)F r=gNm(a);x=cdr(x);i(U xs=x){Uf;P(f,Num,Qnum)r/=gNm(f);}R Nm(r);)
U2(f_sqrt,$$(isNil(x),Qarg);$$(!isNil(cdr(x)),U rev=nil,m=nil;i(U xs=x){Uf;$$(f==QQ,RQ);U r=bc1(f,_sqrt);$$(r==QQ,RQ);rev=cons(r,rev);}
i2(U ps=rev){m=cons(car(ps),m);}Rm;);Uv;$$(v==QQ,RQ);R bc1(v,_sqrt);)
U2(f_mod,$$(isNil(x),Qarg)U a=eval(car(x),y);$$(isNil(cdr(x)),P(a,Num,Qnum);R Nm(fmod(gNm(a),1.0)))U b=eval(car(cdr(x)),y);
$$(T(a)==Pair||T(b)==Pair,R bc2(a,b,_mod))P(a,Num,Qnum)F r=gNm(a);x=cdr(x);i(U xs=x){Uf;P(f,Num,Qnum)r=fmod(r,gNm(f));}R Nm(r);)
U2(f_quote,(V)y;R car(x))U2(f_atom,R isAtom(eval(car(x),y))?tr:nil)
U2(f_eq,$$(isNil(x)||isNil(cdr(x)),Rt)U f=eval(car(x),y);$$(f==QQ,RQ);i(U xs=cdr(x)){U v=eval(car(xs),y);$$(v==QQ,RQ)$$(!eq(f,v),R nil)}Rt;)
U2(f_lt,U f=eval(car(x),y);$$(T(f)!=Num,Qnum)i(U xs=cdr(x)){U nxt=eval(car(xs),y);
$$(T(nxt)!=Num,Qnum)$$(!(gNm(f)<gNm(nxt)),R nil)f=nxt;}Rt;)
U2(f_gt,U f=eval(car(x),y);$$(T(f)!=Num,Qnum)i(U xs=cdr(x)){U nxt=eval(car(xs),y);
$$(T(nxt)!=Num,Qnum)$$(!(gNm(f)>gNm(nxt)),R nil)f=nxt;}Rt;)
U2(f_car,$$(isNil(x),Qarg)U v=eval(car(x),y);$$(Tv!=Pair,Qpair)R car(v);)
U2(f_cdr,$$(isNil(x),Qarg)U v=eval(car(x),y);$$(Tv!=Pair,Qpair)R cdr(v);)
U2(f_cons,R cons(eval(car(x),y),eval(car(cdr(x)),y)))
U2(f_and,$$(isNil(x),Rt)i(U xs=x){U v=eval(car(xs),y);$$(isNil(v),R nil)}Rt;)
U2(f_or,$$(isNil(x),R nil)i(U xs=x){U v=eval(car(xs),y);$$(!isNil(v),Rt)}R nil;)
U2(f_xor,I cnt=0;i(U xs=x){U v=eval(car(xs),y);$$(!isNil(v),cnt++)}R(cnt%2)?tr:nil;)
U2(f_not,$$(isNil(x)||!isNil(cdr(x)),Qarg)U v=eval(car(x),y);R isNil(v)?tr:nil;)
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
W(1){rdt();$$(IF==stdin,break)U expr=rexpr();eval(expr,genv);ready=0;}IF=oldIF;ready=0;R Sm("loaded\n");)
U2(f_list,$$(isNil(x), Qarg)U lst=nil,*tl=&lst;W(!isNil(x)){U e=eval(car(x),y);*tl=cons(e,nil);tl=&((U*)*tl)[2];x=cdr(x);}R lst;)

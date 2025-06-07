#include<string.h> //u incunabulum /if64
#include<stdlib.h> //+ - * / sqrt quote atom eq car cdr cons define lambda if
#include<stdio.h>  //(c)nekoarch 2025 MIT
#include<math.h>   //sqrt
typedef int I;typedef void V,*U;typedef char C;typedef double F;
#define R return
#define Rm R m
#define $(b,a...) if(b){a;}else
#define $$(b,a...) if(b){a;}
#define _(z) ({z;})
#define W(z) while(_(z))
#define Ux U x
#define Uy U y
#define Uz U z
#define U1(nm,a...) U nm(Ux){a;}
#define U2(nm,a...) U nm(Ux,Uy){a;}
#define U3(nm,a...) U nm(Ux,Uy,Uz){a;}
I eq(Ux,Uy);U eval(Ux,Uy);
I Num=1,Sym=2,Pair=3,Nil=4,Clos=5;U nil,genv;
I T(Ux){R*(I*)x;}
U Nm(F x){C*m=malloc(sizeof(I)+sizeof(F));*(I*)m=Num;*(F*)(m+sizeof(I))=x;Rm;}
F gNm(Ux){R *(F*)((C*)x+sizeof(I));}
U Sm(C*s){I L=strlen(s)+1;C*m=malloc(sizeof(I)+L);*(I*)m=Sym;memcpy(m+sizeof(I),s,L);Rm;}
C*gSm(Ux){R(C*)x+sizeof(I);}
U2(cons,U*m=malloc(3*sizeof(U));*(I*)m=Pair;m[1]=x;m[2]=y;Rm)
U1(car,R((U*)x)[1])
U1(cdr,R((U*)x)[2])
U3(closure,C*m=malloc(sizeof(I)+3*sizeof(U));*(I*)m=Clos;U*f=(U*)(m+sizeof(I));f[0]=x;f[1]=y;f[2]=z;Rm)//tg+param+body+env
U1(clop,R((U*)((C*)x+sizeof(I)))[0])
U1(clob,R((U*)((C*)x+sizeof(I)))[1])
U1(cloe,R((U*)((C*)x+sizeof(I)))[2])
I isNil(Ux){R x==nil||T(x)==Nil;}
I isAtom(Ux){R T(x)==Sym||T(x)==Num||isNil(x);}
V pt(Ux){$(isNil(x),printf("nil"))$(T(x)==Num,printf("%g",gNm(x)))$(T(x)==Sym,printf("%s",gSm(x)))$$(T(x)==Pair,printf("(");W(T(x)==Pair){pt(car(x));x=cdr(x);$$(T(x)==Pair,printf(" "))}$$(!isNil(x),printf(" . ");pt(x))printf(")");)}
C token[128];I ready=0;
I space(I c){R c==' '||c=='\f'||c=='\n'||c=='\r'||c=='\t'||c=='\v';}
I digit(I c){R (c<='9')&&(c>='0');}
V rdt(){$$(ready, R)I c;W((c=getchar())!=EOF&&space(c));
$(c==EOF,exit(0));$(c=='('||c==')',token[0]=c;token[1]=0){
I i=0;do {token[i++]=c;c=getchar();}W(c!=EOF&&!space(c)&&c!='('&&c!=')'&&i<127);token[i]=0;$$(c!=EOF,ungetc(c,stdin))}ready=1;}
C*ntk(){rdt();ready=0;R token;}
U rexpr();U rlist(){rdt();$$(!strcmp(token,")"),ready=0;R nil;)ready=1;U f=rexpr();U r=rlist();R cons(f,r);}
U rexpr(){C*t=ntk();$$(!strcmp(t,"("),R rlist())$$(digit(t[0])||(t[0]=='-'&&digit(t[1])),R Nm(strtod(t,NULL)))R Sm(t);}
U2(lookup,for(U e=y;!isNil(e);e=cdr(e)){U b=car(e);$$(T(b)==Pair&&eq(x,car(b)),R cdr(b))}printf("unbound: %s\n",gSm(x));exit(1))
I eq(Ux,Uy){$$(T(x)!=T(y),R 0)$$(T(x)==Sym,R!strcmp(gSm(x),gSm(y)))$$(T(x)==Num,R gNm(x)==gNm(y))R x==y;}
typedef U (*prim_fn)(Ux,Uy);
typedef struct{C*name;prim_fn fn;}prim_entry;
U2(f_add,F s=0;for(U xs=x;!isNil(xs);xs=cdr(xs)){U v=eval(car(xs),y);$$(T(v)!=Num,printf("expect num\n");exit(1))s+=gNm(v);}R Nm(s))
U2(f_minus,$$(isNil(x),printf("expect arg\n");exit(1))U a1=eval(car(x),y);$$(T(a1)!=Num,printf("expect num\n");exit(1))F r=gNm(a1);
x=cdr(x);$$(isNil(x),R Nm(-r))for(;!isNil(x);x=cdr(x)){U v=eval(car(x),y);$$(T(v)!=Num,printf("expect num\n");exit(1))r-=gNm(v);}R Nm(r);)
U2(f_mul,F p=1;for(U xs=x;!isNil(xs);xs=cdr(xs)){U v=eval(car(xs),y);$$(T(v)!=Num,printf("expect num\n");exit(1))p*=gNm(v);}R Nm(p))
U2(f_div,$$(isNil(x),printf("expect arg\n");exit(1))U a1=eval(car(x),y);$$(T(a1)!=Num,printf("expect num\n");exit(1))F r=gNm(a1);
x=cdr(x);$$(isNil(x),R Nm(1.0/r))for(;!isNil(x);x=cdr(x)){U v=eval(car(x),y);$$(T(v)!=Num,printf("expect num\n");exit(1))r/=gNm(v);}R Nm(r))
U2(f_sqrt,$$(!isNil(cdr(x)),printf("expect arg\n");exit(1);)U v=eval(car(x),y);$$(T(v)!=Num,printf("expect num\n");exit(1))R Nm(sqrt(gNm(v))))
U2(f_quote,(V)y;R car(x))
U2(f_atom,R isAtom(eval(car(x),y))?Sm("t"):nil)
U2(f_eq,U a=eval(car(x),y),b=eval(car(cdr(x)),y); R eq(a,b)?Sm("t"):nil)
U2(f_car,R car(eval(car(x),y)))
U2(f_cdr,R cdr(eval(car(x),y)))
U2(f_cons,R cons(eval(car(x),y),eval(car(cdr(x)),y)))
U2(f_define,U f=car(x);$(T(f)==Sym,U ph=cons(f,nil);genv=cons(ph,genv);U val=eval(car(cdr(x)),genv);((U*)ph)[2]=val;R f){U fname=car(f),p=cdr(f),body=car(cdr(x));
U ph=cons(fname,nil);genv=cons(ph,genv);U clo=closure(p,body,genv);((U*)ph)[2]=clo;R fname;})
U2(f_lambda,R closure(car(x),car(cdr(x)),y))
U2(f_if,U c=eval(car(x),y);$(!isNil(c),R eval(car(cdr(x)),y)){R eval(car(cdr(cdr(x))),y);})
prim_entry table[]={
{"+",f_add},{"-",f_minus},{"*",f_mul},{"/",f_div},{"sqrt",f_sqrt},
{"quote",f_quote},{"atom",f_atom},{"eq",f_eq},{"car",f_car},
{"cdr",f_cdr},{"cons",f_cons},{"define",f_define},{"lambda",f_lambda},{"if",f_if},{NULL,NULL}};
U eval(Ux,Uy){$$(T(x)==Sym,R lookup(x,y))$$(T(x)==Num||isNil(x),R x)
U op=car(x),args=cdr(x);$$(T(op)==Sym,C*s=gSm(op);for(prim_entry *p=table;p->name;p++){$$(!strcmp(s,p->name),R p->fn(args,y))})
U f=eval(op,y);$$(T(f)!=Clos,printf("expect function\n");exit(1))U params=clop(f),body=clob(f),e0=cloe(f),new_env=e0,xs=args;
for(U ps=params;!isNil(ps);ps=cdr(ps),xs=cdr(xs)){$$(isNil(xs),printf("expect arg\n");exit(1))U val=eval(car(xs),y);new_env=cons(cons(car(ps),val),new_env);}R eval(body,new_env);}
I main(){nil=malloc(sizeof(int));*(I*)nil=Nil;genv=nil;
printf("u/incunabulum (c)nekoarch "__DATE__"\n");
W(1){printf("  ");U expr=rexpr();U res=eval(expr,genv);pt(res);printf("\n");}R 0;}

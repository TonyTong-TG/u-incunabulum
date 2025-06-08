#include<string.h> //u incunabulum /if64
#include<stdlib.h> //+ - * / < > sqrt quote atom eq car cdr cons and or not xor define defmacro lambda if cond load #t #nil
#include<stdio.h>  //(c)nekoarch 2025 MIT
#include<math.h>   //sqrt
typedef int I;typedef void V,*U;typedef char C;typedef double F;
#define Z static
#define R return
#define Rm R m
#define $(b,a...) if(b){a;}else
#define $$(b,a...) if(b){a;}
#define _(z) ({z;})
#define W(z) while(_(z))
#define i(a...) for(a;!isNil(xs);xs=cdr(xs))
#define Ux U x
#define Uy U y
#define Uz U z
#define U1(nm,a...) U nm(Ux){a;}
#define U2(nm,a...) U nm(Ux,Uy){a;}
#define U3(nm,a...) U nm(Ux,Uy,Uz){a;}
#define Qnum printf("expect num\n");R QQ
#define Qarg printf("expect arg\n");R QQ
#define Qpair printf("expect pair\n");R QQ
I eq(Ux,Uy);U eval(Ux,Uy);
I Num=1,Sym=2,Pair=3,Nil=4,Clos=5;Z FILE *IF=NULL;U nil,genv,macenv,QQ;//slient
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
V pt(Ux){$$(x==QQ,return)$(isNil(x),printf("#nil"))$(T(x)==Num,printf("%g",gNm(x)))$(T(x)==Sym,printf("%s",gSm(x)))$$(T(x)==Pair,printf("(");W(T(x)==Pair){pt(car(x));x=cdr(x);$$(T(x)==Pair,printf(" "))}$$(!isNil(x),printf(" . ");pt(x))printf(")");)}
C token[128];I ready=0;
I space(I c){R c==' '||c=='\f'||c=='\n'||c=='\r'||c=='\t'||c=='\v';}
I digit(I c){R (c<='9')&&(c>='0');}
V rdt(){$$(ready, R)I c;W((c=fgetc(IF))!=EOF&&space(c));
$(c==EOF,$$(IF!=stdin,fclose(IF);IF=stdin;ready=0;R)exit(0));$(c=='('||c==')'||c=='\'',token[0]=c;token[1]=0;ready=1;R){I i=0;token[i++]=c;W((c=fgetc(IF))!=EOF&&!space(c)&&c!='('&&c!=')'&&i<127){token[i++]=c;}token[i]=0;$$(c!=EOF,ungetc(c,IF))}ready=1;}
C*ntk(){rdt();ready=0;R token;}
U rexpr();U rlist(){rdt();$$(!strcmp(token,")"),ready=0;R nil;)ready=1;U f=rexpr();U r=rlist();R cons(f,r);}
U rexpr(){C*t=ntk();$$(!strcmp(t,"'"),U qtd=rexpr();R cons(Sm("quote"),cons(qtd,nil)))$$(!strcmp(t,"#t"),R Sm("#t"))$$(!strcmp(t,"#nil"),R nil)$$(!strcmp(t,"("),R rlist())$$(digit(t[0])||(t[0]=='-'&&digit(t[1])),R Nm(strtod(t,NULL)))R Sm(t);}
U2(lookup,i(U xs=y){U b=car(xs);$$(T(b)==Pair&&eq(x,car(b)),R cdr(b))}printf("unbound: %s\n",gSm(x));R QQ)
I eq(Ux,Uy){$$(T(x)!=T(y),R 0)$$(T(x)==Sym,R!strcmp(gSm(x),gSm(y)))$$(T(x)==Num,R gNm(x)==gNm(y))R x==y;}
typedef U (*prim_fn)(Ux,Uy);
typedef struct{C*name;prim_fn fn;}prim_entry;
U2(f_add,F s=0;i(U xs=x){U v=eval(car(xs),y);$$(T(v)!=Num,Qnum)s+=gNm(v);}R Nm(s))
U2(f_minus,$$(isNil(x),Qarg)U a1=eval(car(x),y);$$(T(a1)!=Num,Qnum)F r=gNm(a1);
x=cdr(x);$$(isNil(x),R Nm(-r))for(;!isNil(x);x=cdr(x)){U v=eval(car(x),y);$$(T(v)!=Num,Qnum)r-=gNm(v);}R Nm(r);)
U2(f_mul,F p=1;i(U xs=x){U v=eval(car(xs),y);$$(T(v)!=Num,Qnum)p*=gNm(v);}R Nm(p))
U2(f_div,$$(isNil(x),Qarg)U a1=eval(car(x),y);$$(T(a1)!=Num,Qnum)F r=gNm(a1);
x=cdr(x);$$(isNil(x),R Nm(1.0/r))for(;!isNil(x);x=cdr(x)){U v=eval(car(x),y);$$(T(v)!=Num,Qnum)r/=gNm(v);}R Nm(r))
U2(f_sqrt,$$(!isNil(cdr(x)),Qarg;)U v=eval(car(x),y);$$(T(v)!=Num,Qnum)R Nm(sqrt(gNm(v))))
U2(f_quote,(V)y;R car(x))
U2(f_atom,R isAtom(eval(car(x),y))?Sm("#t"):nil)
U2(f_eq,U a=eval(car(x),y),b=eval(car(cdr(x)),y); R eq(a,b)?Sm("#t"):nil)
U2(f_lt,U f=eval(car(x),y);$$(T(f)!=Num,Qnum)i(U xs=cdr(x)){U nxt=eval(car(xs),y);$$(T(nxt)!=Num,Qnum)$$(!(gNm(f)<gNm(nxt)),R nil)f=nxt;}R Sm("#t");)
U2(f_gt,U f=eval(car(x),y);$$(T(f)!=Num,Qnum)i(U xs=cdr(x)){U nxt=eval(car(xs),y);$$(T(nxt)!=Num,Qnum)$$(!(gNm(f)>gNm(nxt)),R nil)f=nxt;}R Sm("#t");)
U2(f_car,$$(isNil(x),Qarg)U v=eval(car(x),y);$$(T(v)!=Pair,Qpair)R car(v);)
U2(f_cdr,$$(isNil(x),Qarg)U v=eval(car(x),y);$$(T(v)!=Pair,Qpair)R cdr(v);)
U2(f_cons,R cons(eval(car(x),y),eval(car(cdr(x)),y)))
U2(f_and,$$(isNil(x),R Sm("#t"))i(U xs=x){U v=eval(car(xs),y);$$(isNil(v),R nil)}R Sm("#t");)
U2(f_or,$$(isNil(x),R nil)i(U xs=x){U v=eval(car(xs),y);$$(!isNil(v),R Sm("#t"))}R nil;)
U2(f_xor,I cnt=0;i(U xs=x){U v=eval(car(xs),y);$$(!isNil(v),cnt++)}R(cnt%2)?Sm("#t"):nil;)
U2(f_not,$$(isNil(x)||!isNil(cdr(x)),printf("not: expect 1 arg\n");R QQ)U v=eval(car(x),y);R isNil(v)?Sm("#t"):nil;)
U2(f_define,U f=car(x);$(T(f)==Sym,U ph=cons(f,nil);genv=cons(ph,genv);U val=eval(car(cdr(x)),genv);((U*)ph)[2]=val;R f){U fname=car(f),p=cdr(f),body=car(cdr(x));
U ph=cons(fname,nil);genv=cons(ph,genv);U clo=closure(p,body,genv);((U*)ph)[2]=clo;R fname;})
U2(f_lambda,R closure(car(x),car(cdr(x)),y))
U2(f_if,U c=eval(car(x),y);$(!isNil(c),R eval(car(cdr(x)),y)){R eval(car(cdr(cdr(x))),y);})
U2(f_cond,i(U xs=x){U ps=car(xs);$$(isNil(ps)||isNil(cdr(ps)),printf("bad clause\n");R QQ)U t=car(ps),b=cdr(ps);
$(T(t)==Sym&&!strcmp(gSm(t),"else"),$$(!isNil(cdr(xs)),printf("cond: else must be the last\n");R QQ))
{U res=eval(t,y);$$(isNil(res),continue)}U re=nil;for(U seq=b;!isNil(seq);seq=cdr(seq)){re=eval(car(seq),y);}R re;}R nil;)
U2(f_macro,$$(isNil(x)||isNil(cdr(x))||isNil(cdr(cdr(x))),printf("bad macro syntax\n");R QQ)U nm=car(x),rst=cdr(x),p=car(rst),bdy=car(cdr(rst)),tmp=closure(p,bdy,y);macenv=cons(cons(nm,tmp),macenv);R nm;)
U2(f_load,$$(isNil(x),printf("load: expect filename\n");R QQ)U fn=eval(car(x),y);$$(T(fn)!=Sym,printf("load: filename must be symbol\n");R QQ)
FILE *oldIF=IF;IF=fopen(gSm(fn),"r");$$(!IF,perror(gSm(fn));IF=oldIF;R QQ)ready=0;W(1){rdt();$$(IF == stdin,break)U expr=rexpr();eval(expr,genv);ready=0;}IF=oldIF;ready=0;R QQ;)
prim_entry table[]={
{"+",f_add},{"-",f_minus},{"*",f_mul},{"/",f_div},{"sqrt",f_sqrt},
{"quote",f_quote},{"atom",f_atom},{"eq",f_eq},{"car",f_car},
{"cdr",f_cdr},{"cons",f_cons},{"define",f_define},{"lambda",f_lambda},
{"if",f_if},{"<",f_lt},{">",f_gt},{"cond",f_cond},{"and",f_and},{"defmacro",f_macro},
{"or",f_or},{"xor",f_xor},{"not",f_not},{"load", f_load},{NULL,NULL}};
U lfind(Ux,Uy){i(U xs=y){U bind=car(xs);$$(T(bind)==Pair&&eq(x,car(bind)),R cdr(bind))}R nil;}
U subst(Ux, Uy){$$(T(x)==Sym,U v=lfind(x,y);R v==nil?x:v)$$(T(x)==Pair,R cons(subst(car(x),y),subst(cdr(x),y)))R x;}
U expand(Ux){$$(T(x)!=Pair,R x)U hd = car(x);
i(U xs=macenv){U def=car(xs),name=car(def);if (eq(hd,name)){U rest=cdr(def),params=clop(rest),tem=clob(rest),penv=nil,args=cdr(x);for(U ps=params;!isNil(ps);ps=cdr(ps),args=cdr(args)){penv=cons(cons(car(ps),car(args)),penv);}U inst=subst(tem, penv);R expand(inst);}}R cons(expand(hd),expand(cdr(x)));}
U eval(Ux,Uy){x=expand(x);$$(x==QQ,R QQ)$$(T(x)==Sym,R lookup(x,y))$$(T(x)==Num||isNil(x),R x)
U op=car(x),args=cdr(x);$$(T(op)==Sym,C*s=gSm(op);for(prim_entry *p=table;p->name;p++){$$(!strcmp(s,p->name),R p->fn(args,y))})
U f=eval(op,y);$$(T(f)!=Clos,printf("expect function\n");R QQ)U params=clop(f),body=clob(f),e0=cloe(f),new_env=e0,xs=args;
for(U ps=params;!isNil(ps);ps=cdr(ps),xs=cdr(xs)){$$(isNil(xs),Qarg)U val=eval(car(xs),y);new_env=cons(cons(car(ps),val),new_env);}R eval(body,new_env);}
I main(I ac,C**av){IF=stdin;$$(ac>1,$$(!freopen(av[1],"r",stdin),perror(av[1]);return 1))QQ=malloc(1);nil=malloc(sizeof(I));*(I*)nil=Nil;genv=nil;macenv=nil;U t = Sm("#t");genv=cons(cons(t,t),genv);$$(ac==1,printf("u/incunabulum (c)nekoarch "__DATE__"\n"))
W(1){printf("  ");U expr=rexpr();U res=eval(expr,genv);pt(res);printf("\n");}R 0;}

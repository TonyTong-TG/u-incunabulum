#include "u.h" // u/incunabulum MIT f(i)64 glibc
#define ver "0.3 "
V rdt(){$$(ready, R)I c;W((c=fgetc(IF))!=EOF&&space(c));$(c==EOF,$$(IF!=stdin,fclose(IF);IF=stdin;ready=0;R)exit(0))
$(c=='"',I i=0;token[i++]=c;W((c=fgetc(IF))!=EOF&&c!='"'){token[i++]=c;$$(i>=127,break)}token[i++]=c;token[i]=0;ready=1;R;)
$(c=='('||c==')'||c=='\'',token[0]=c;token[1]=0;ready=1;R){I i=0;token[i++]=c;
W((c=fgetc(IF))!=EOF&&!space(c)&&c!='('&&c!=')'&&i<127){token[i++]=c;}token[i]=0;$$(c!=EOF,ungetc(c,IF))}ready=1;}
C*ntk(){rdt();ready=0;R token;}
U rexpr();U rlist(){rdt();$$(!strcmp(token,")"),ready=0;R nil;)ready=1;U f=rexpr();U r=rlist();R cons(f,r);}
U rexpr(){C*t=ntk();$$(t[0]=='"'&&t[strlen(t)-1]=='"',R Sm(t))$$(!strcmp(t,"'"),U qtd=rexpr();R cons(Sm("quote"),cons(qtd,nil)))
$$(!strcmp(t,"#t"),R tr)$$(!strcmp(t,"#nil"),R nil)$$(!strcmp(t,"("),R rlist())$$(digit(t[0])||(t[0]=='-'&&digit(t[1])),R Nm(strtod(t,NULL)))R Sm(t);}
U2(lookup,i(U xs=y){U b=car(xs);$$(T(b)==Pair&&eq(x,car(b)),R cdr(b))}printf("unbound: %s\n",gSm(x));RQ)
U bc2(Ux,Uy,U(*op)(U,U)){$$(x==QQ||y==QQ,RQ)I ax=isAtom(x),ay=isAtom(y);
$$(ax&&ay,$$(Tx!=Num||Ty!=Num,Qnum);R op(x,y))
$$(ax||ay,I xatm=ax;U lst=xatm?y:x,hd=nil,*tl=&hd;$$(!isPropLst(lst),Qlst)W(!isNil(lst)){
U a=xatm?x:car(lst),b=xatm?car(lst):y;U r=bc2(a,b,op);$$(r==QQ,RQ)
U n=cons(r,nil);*tl=n;tl=&((U*)n)[2];lst=cdr(lst);}R hd;)
{$$(!(isPropLst(x)&&isPropLst(y)),Qlst)U xs=x,ys=y,hd=nil,*tl=&hd;W(!isNil(xs)&&!isNil(ys)){U r=bc2(car(xs),car(ys),op);$$(r==QQ,RQ)
U n=cons(r,nil);*tl=n; tl=&((U*)n)[2];xs=cdr(xs); ys=cdr(ys);}$$(!isNil(xs)||!isNil(ys),Qlen)R hd;}} //binary
U bc1(Ux,U(*op)(U)){$$(x==QQ,RQ)$$(isAtom(x),P(x,Num,Qnum)R op(x))$$(!isPropLst(x),Qlst)U m=nil,*tl=&m;
i(U xs=x){U e=car(xs);U r=bc1(e,op);$$(r==QQ,RQ);U n=cons(r,nil);*tl=n;tl=&((U*)n)[2];}Rm;} //unary
typedef U (*prim_fn)(Ux,Uy);
typedef struct{C*name;prim_fn fn;}prim_entry;
prim_entry table[]={
{"+",f_add},{"-",f_minus},{"*",f_mul},{"/",f_div},{"sqrt",f_sqrt},{"%",f_mod},
{"quote",f_quote},{"atom",f_atom},{"eq",f_eq},{"car",f_car},
{"cdr",f_cdr},{"cons",f_cons},{"define",f_define},{"lambda",f_lambda},{"list",f_list},
{"if",f_if},{"<",f_lt},{">",f_gt},{"cond",f_cond},{"and",f_and},{"defmacro",f_macro},
{"or",f_or},{"xor",f_xor},{"not",f_not},{"load", f_load},{NULL,NULL}};
U lfind(Ux,Uy){i(U xs=y){U bind=car(xs);$$(T(bind)==Pair&&eq(x,car(bind)),R cdr(bind))}R nil;}
U subst(Ux,Uy){$$(T(x)==Sym,U v=lfind(x,y);R v==nil?x:v)$$(T(x)==Pair,R cons(subst(car(x),y),subst(cdr(x),y)))R x;}
U expand(Ux){$$(T(x)!=Pair,R x)U hd = car(x);
i(U xs=macenv){U def=car(xs),name=car(def);if (eq(hd,name)){U rest=cdr(def),params=clop(rest),tem=clob(rest),penv=nil,args=cdr(x);
for(U ps=params;!isNil(ps);ps=cdr(ps),args=cdr(args)){penv=cons(cons(car(ps),car(args)),penv);}
U inst=subst(tem, penv);R expand(inst);}}R cons(expand(hd),expand(cdr(x)));}//unsafe: may infinitely expand or expand in quote/define/macro contexts
U eval(Ux,Uy){x=expand(x);$$(x==QQ,R QQ)$$(T(x)==Sym,C*s=gSm(x);$$(s[0]=='"'&&s[strlen(s)-1]=='"',R x)R lookup(x,y))
$$(Tx==Num||isNil(x)||Tx==True,R x)U op=car(x),args=cdr(x);
$$(T(op)==Sym,C*s=gSm(op);for(prim_entry *p=table;p->name;p++){$$(!strcmp(s,p->name),R p->fn(args,y))})
U f=eval(op,y);$$(f==QQ||T(f)!=Clos,Qfun)U params=clop(f),body=clob(f),e0=cloe(f),new_env=e0,xs=args;
for(U ps=params;!isNil(ps);ps=cdr(ps),xs=cdr(xs)){$$(isNil(xs),Qarg)U val=eval(car(xs),y);$$(val==QQ,RQ)new_env=cons(cons(car(ps),val),new_env);}R eval(body,new_env);}
I main(I ac,C**av){IF=stdin;$$(ac>1,$$(!freopen(av[1],"r",stdin),perror(av[1]);R 1))
QQ=malloc(1);nil=malloc(sizeof(I));tr=malloc(sizeof(I));*(I*)nil=Nil;*(I*)tr=True;genv=nil;macenv=nil;genv=cons(cons(tr,tr),genv);
$$(ac==1,printf("u/incunabulum (c)nekoarch "ver __DATE__"\n"))W(1){printf("  ");U expr=rexpr();
$$(T(expr)==Sym&&!strcmp(gSm(expr),":help"),printf("%s\n",man);ready=0;continue)U res=eval(expr,genv);pt(res);printf("\n");}R 0;}

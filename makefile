CC		= gcc
YACC	= yacc
LEX		= lex

comp:	y.tab.c lex.yy.c ast.c comp3.c cfg.c
	$(CC) lex.yy.c y.tab.c ast.c comp3.c cfg.c -o comp -ll

y.tab.c: yacc.y
	$(YACC) -d yacc.y

lex.yy.c: lex.l y.tab.h
	$(LEX) lex.l

clean:
	rm comp lex.yy.c y.tab.c y.tab.h

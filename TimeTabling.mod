float temp;
string output_fileName = ...;
execute
{
  cplex.mipdisplay=3;
  //cplex.mipemphasis=1;
  cplex.tilim= 600;
  // cplex.threads = 4;
  
  var before = new Date();
  temp = before.getTime();
}
// Turmas 1..10
{int} T = ...;
// Componentes curriculares
{string} C = ...;
// Dias da semana 2..7
{int} D = ...;
// Conjunto dos horarios em que uma aula pode ser realizada
{int } S = ...;
// conjunto de locais disponiveis
{string } L =...;
// conjunto dos turnos
{int} F = ...;
// tuplas representando horarios S que pertencem ao turno F
tuple SF {
	int s;
	int f;
}
// tupla Semana e Turno sf = {<1,1>, <2,1>, <3,1>, <4,2>, <5,2>, <6,2>, <7,3>, <8,3>};
{SF} sf = ...;

{int} SEM = ...; // conjunto de semestres

int nf[F] = ...; // numero de disciplinas por turno

tuple Csem {
	string c;
	int sem;
}
// tupla Componente e Semestre <"PC", 1>
{Csem} csem = ...;

tuple cDiaRestricao {
    string c;
    int d;
}

tuple cDiaSlotRestricao {
    string c;
    int d;
    int s;
}

{cDiaRestricao} cDiaRestricoes = ...; 
{cDiaSlotRestricao} cDiaSlotRestricoes = ...;

int cl[L] = ...;
int h = ...;
int  h_total[C] = ...;
int  v[C, F] =  ...;
string sname[S] = ...;

/*
Se a turma t tem aula da componente c no dia d,
horário s no local l
*/
dvar boolean x[T][C][D][S][L];

/*
se a turma t do componente c foi aberta no local l
*/
dvar boolean y[T][C][L];

/*
se uma componente já foi alocada em um dia e horario
*/
dvar boolean z[C][D][S];

/*
Minimizar o quantitativo de turmas
*/
minimize
	sum(t in T, c in C, l in L) 1 / cl[l] * y[t][c][l];

subject to {
	/*
	Somente turmas abertas tem aula
	*/
	forall(t in T, c in C, d in D, s in S, l in L)
		ct01:
			x[t, c, d, s, l] <= y[t, c, l];

	/*
	No máximo um local recebe uma turma de uma componente
	*/  	
	forall(t in T, c in C)
		ct02:	
			sum(l in L) y[t, c, l] <= 1;

	/*
	No mesmo dia e horário um local só pode ser usado uma vez
	*/	  	
	forall(l in L, d in D, s in S)
		ct03:
			sum(t in T, c in C) x[t, c, d, s, l] <= 1;

	/*
	A demanda de vagas por uma componente tem de ser atendida quando a turma é aberta
	*/
	forall(c in C, f in F)
		ct04:
			sum(t in T, d in D, <s, f1> in sf, l in L: f1 == f) ((cl[l] * x[t, c, d, s, l]) / (h_total[c] / h)) >= v[c, f];

	/*Não tem alocação nesse slot se não precisa de vaga naquele turno*/
	forall(c in C, f in F, t in T, d in D, <s, f1> in sf, l in L: f1 == f)
		ct11:
			x[t, c, d, s, l] <= v[c, f];

	/*
	A demanda por carga horária tem de ser atendida em cada turma
	*/
	forall(t in T, c in C)
		ct05:
			sum(d in D, s in S, l in L) h * x[t, c, d, s, l] == h_total[c] * sum(l in L) y[t, c, l];

	/*
	As aulas de uma mesma turma são sempre no mesmo horário
	*/
	forall(t in T, c in C, d1 in D, d2 in D, s1 in S, s2 in S: s1 != s2)
		ct08:
			sum(l in L) (x[t, c, d1, s1, l] + x[t, c, d2, s2, l]) <= 1;

	/*
	Ordem de abertura de turmas, começar da turma 1
	*/
	forall(t1 in T, t2 in T, c in C: t1 < t2)
		ct10:
			sum(l in L) y[t1][c][l] >= sum(l in L) y[t2][c][l];

	/*
	Restrinja que ocorra aula nesse dia: ("LoP", 6) => "LoP" a matéria, 2 referente a sexta 
	*/
	forall(cd in cDiaRestricoes, c in C, d in D)
		ct12:
			(cd.c == c && cd.d == d) => (sum(t in T, l in L, s in S) x[t, c, d, s, l] == 0);

	/*
	Restrinja o dia e horario de aula de uma componente: ("LoP", 2, 1) => "LoP" a matéria, 2 referente a segunda e 1 referente a M12
	*/
	forall(ct in cDiaSlotRestricoes, c in C, s in S, d in D)
		ct13:
			(ct.c == c && ct.d == d && ct.s == s) => (sum(t in T, l in L) x[t, c, d, s, l] == 0);

	/*
	Remover do modelo de alocação o sábado T56, N12 e N34
	*/
	forall(t in T, c in C, s in S, l in L: (s >= 6 && s <= 8)) {
		x[t, c, 7, s, l] == 0;
	}

	// Modificações dia 18/11
	/*
	Se a componente c tem aula no dia d e horario s, então ela tem aula no dia d e horario s+1
	*/
	forall(t in T, c in C, d in D, s in S, l in L)
		ctT:
			z[c, d, s] >= x[t, c, d, s, l];

	forall(c in C, d in D, s in S)
		ctT2:
			z[c, d, s] <= sum(t in T, l in L) x[t, c, d, s, l];

	forall(c in C, t in T, d1 in D, s in S, d2 in D, l in L: (d1 == d2 - 1 || d1 == d2 - 3 || d1 == d2 - 4) && d1 < d2)
		ctT3:
			x[t, c, d1, s, l] + x[t, c, d2, s, l] <= 1;
	
	/*
		Restrição que garante que se uma componente tem aula no dia 
		d e horario s, então ela tem aula no dia d e horario s+1
	*/
	forall(c1 in C, c2 in C, d in D, s in S: c1 != c2)
		ctT4:
		 ((sum(sc in csem: sc.c == c1) sc.sem == sum(sc in csem: sc.c == c2) sc.sem)) => z[c1, d, s] + z[c2, d, s] <= sum(<s1, f1> in sf: s1 != s) z[c1, d, s1] + sum(<s2, f2> in sf: s2 != s) z[c2, d, s2];

	// Modificações dia 19/11

	forall(c in C, s in S)
		ctT5:
			sum(d in D) z[c, d, s] <= h_total[c] / h; 

	// restrição que limita o max de disciplinas de mesmo semestre por horario por turno
	forall(sem in SEM, d in D, <s, f> in sf)
		ctT6:
			sum(c in C, sc in csem: sc.c == c && sc.sem == sem) z[c, d, s] <= nf[f];
		
}

tuple Turmas{
	int sem;
	int t; 
	string c; 
	int d;
	string s;
	string l;
	int cl; 
};
{Turmas} turmas= {<sem, t,c,d, sname[s], l, cl[l]> | <c, sem> in csem, t in T, d in D, s in S, l in L: y[t,c,l]==1 && x[t, c, d, s, l]==1};

execute {
   var solutionCost = cplex.getObjValue();
   var lowerBound = cplex.getBestObjValue();
   var gap = (solutionCost - lowerBound) / solutionCost * 100;
   var after = new Date();
   var executionTime = (after.getTime()-temp)/ 1000;
	 writeln("Turmas=", turmas)
   
   var ofile = new IloOplOutputFile(output_fileName);
   ofile.writeln("Custo da solucao =", solutionCost);
   ofile.writeln("Custo do limitante inferior =", lowerBound);
   ofile.writeln("Gap =", gap, "%");
   ofile.writeln("Tempo de execução total =", executionTime, " seconds");
   ofile.writeln("Turmas=", turmas);
   ofile.close();
}

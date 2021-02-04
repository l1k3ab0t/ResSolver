# ResSolver
### Simple Resolution Solvers for Propositional and First Order Logic


#### Usage
`python fol_solver.py f`

`fol_solver.py` expects that the input file `f` is formatted as follows:
```
S(1, 1), S(f(b), f(b))
!S(1, 1)
```
where  `S` is a Literal, `f` a Function, `b` a Constant and `1` a Variable.

The Proof is printed both in human-readable Notation and in LaTeX.

The output for the example above is:
```
[[Sol(X1, X1), Sol(f(a), f(a))], [!Sol(X1, X1)]]
\begin{array}{lll}
1. & \{ Sol(f(a), f(a)), Sol(X1, X1)\}& \text{premise} \\
2. & \{ \neg Sol(X1, X1)\}& \text{premise} \\
3. & \{ \} & \text{(Res) with from 1 and 2 with $\{ Sol(f(a), f(a)), Sol(X1, X1) \}$ and $\{ \neg Sol(X1, X1) \}$}\\ 
&&\text{ renaming $\{X_{1}\to X_{2} \}$, and mgu $\{X_{1}\to f(a), X_{2}\to f(a) \}$} \\
\end{array}
1.	Sol(f(a), f(a)), Sol(X1, X1)			premise
2.	!Sol(X1, X1)			premise
3.	{}			(Res) from 1 and 2 with {Sol(f(a), f(a)), Sol(X1, X1)} and {!Sol(X1, X1)}, renaming {X1->X2}, and mgu {X1->f(a),X2->f(a)}
```

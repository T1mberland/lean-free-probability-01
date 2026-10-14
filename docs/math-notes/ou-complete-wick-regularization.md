# Actual complete Wick and native OU regularization

Root sources `f97326e`, `e52f41d`, `384a532`, `2950c98` use the checked
homogeneous completion (`453b325`, `0eb17cf`) and original-family word
representation (PR56). Worker native image sources `359200d`, `0554f84`
and notes `9881bb9` supply the exact normclosed-algebra equivalence.

For every complete coefficient vector f, the actual series
`R_z(f)=Σ_n z^n W_n((lengthDecomposition f)_n)` converges in operator norm
when |z|<1. It is a genuine bounded linear map into bounded operators,
not a formal expansion or merely coordinate convergence. The homogeneous
bound n+1 and coordinate contraction give `‖R_z‖≤(1−|z|)^−2`.
Every summand belongs to the original closed word algebra, so its norm limit
does too. At z=exp(−t), its vacuum is exactly the completed word OU damping.

The actual whole-family double-commutant representation σ has the same
damped vacuum, and both σ(P_t(T)) and R_z(coeff(T)) commute with all original
right fields. Genuine vacuum separation identifies these operators. This
does not require σ to be onto the full word von Neumann algebra. Its native
Cstar image equality then shows P_t(T) belongs to the original native family
algebra for every t>0. Faithful isometry gives the actual state-L2 bound
`‖P_t(T)‖≤(1−exp(−t))^−2 ‖TΩ‖`.

Theorems apply to every orthonormal family in an arbitrary complete complex
Hilbert space, including proper, empty and uncountable families. The bound
does not depend on alphabet or ambient dimension. The verification usage
specializes to t=log 2, giving factor four.

An initial nested-CLM norm proof hit elaboration/typeclass limits. Explicit
codomains and `ContinuousLinearMap.opNorm_smul_le` resolved the obstruction;
no resource limit was increased. Direct principal axiom audits use only
propext, Classical.choice and Quot.sound. All precise statements were reviewed.

This establishes scalar state-L2 to operator regularization. It does not
establish complete matrix entropy, noncommutative L1 extension or the full
Goal10. The separate positive suffix-Gram plan records the exact finite
matrix identity and mixed-degree entropy obligations still being developed.

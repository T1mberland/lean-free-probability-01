# Centered Haar trace estimates: reviewed mathematical plan

This is an unproved execution plan, not an integrated Lean theorem.
The actual stable Weingarten formula and distance-sensitive inverse bounds
are verified separately. Actual paired-network orientation, matrix norms
and the following trace estimates still require formalization.

For m nonempty centered alternating trace words with total halfdegree r,
reduce each row/column pairing contraction to genuine cycle traces. Prove
each of the 2r deterministic matrix factors occurs exactly once. Transposes
may occur; their trace and actual Euclidean operator norm must be proved
preserved. Any singleton cycle then vanishes because its matrix is centered.
If no singleton occurs, every cycle uses at least two factors, so the total
row/column cycle count is at most r. True operator norm trace bounds give
contraction at most N^(r-m) times the deterministic norm product.

The verified true inverse estimate gives |W(p,q)| <= C_r N^(-r-d(p,q)).
For N>=1, the resulting finite pairing sum is O(N^-m). No noncrossing
geodesic classification is needed for this centered estimate. Empty trace
words equal one and must not be counted in m.

For one fixed nonempty trace word Z_N, rewrite its conjugate as the reversed
adjoint alternating trace word using actual cyclic trace and real orthogonal
U. The two-word bound yields E|Z_N|^2 <= C/N^2 when deterministic operator
norms are uniform in N. First Borel-Cantelli would imply Z_N ->0 almost
surely on any common probability space with the correct Haar marginals;
independence across dimensions is unnecessary. Simultaneous assertions must
use a countable word family or a separately proved separability argument.

Multiple independent Haar colors and full limiting joint laws require further
conditional-integration and product-trace control. Strong resolvent convergence
is a distinct Goal9 obligation. None is claimed complete by this plan.

The read-only mathematical reviewer validated this argument and its scope.
Worker A is proving actual Euclidean operator-norm network bounds next;
paired half-cycle orientation and factor exhaustion remain the key blockers.

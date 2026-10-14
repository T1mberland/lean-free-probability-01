# Actual suffix representation and commutant prerequisites

## Verified completed-Hilbert-space construction

b4a884a packages the existing actual word reversal as an onto complex Hilbert
unitary on arbitrary completed word spaces, including empty alphabets. Its
creator, adjoint annihilator, and real-field conjugations identify the existing
literal right operators.

b71f9c3 constructs source and adapted-target reversals and the genuine unital
injective suffix embedding on ALL bounded source tensor-Fock operators. The
actual full-space identity R_target Γ(V) = Γ(V) R_source follows from reversal
on the complete empty-tail sector.

c47e931 proves actual suffix(T) Γ(V) = Γ(V) T for EVERY source bounded T, the
literal full compression left inverse, and actual ambient vacuum expectation
preservation. No polynomial restriction or orthonormal-family assumption enters
these full-operator representation identities.

## Verified commutation scopes

178134c proves actual prefix amplification commutes with every outside right
creator and annihilator. Appending an outside letter changes only the tail
coordinate, even for infinite prefix amplitudes. Adjoint transport gives the
annihilator result for arbitrary source operators.

5f85afe gives the literal word suffix representation and proves that every
suffix operator commutes with every outside LEFT creator and its adjoint.
No source-field commutant assumption is needed for outside letters.

eb3108a proves the included word-field commutant result: if B commutes with a
specified source real field, its word suffix image commutes with the literal
included left field. Actual complete-sector right-field calculations cover
empty tails and every outside-starting tail, including the annihilation
boundary. No finite-support approximation is assumed in the final statement.

c1d50cb transports the word suffix representation exactly to the fixed literal
tensor Fock spaces. It gives actual outside adapted-basis creator/annihilator
commutation and chosen full-source-basis real-field commutant transport.

c86fe6e strengthens outside commutation to EVERY geometric vector k orthogonal
to V(H), for every bounded source B. In the full target Hilbert-basis expansion
of k the included coefficients vanish by orthogonality; the remaining outside
creator commutants extend through convergent basis sums. Genuine adjoints give
all orthogonal-complement annihilators.

## Verification and implementation decisions

Each final module was focused compiled under the shared lock with exit 0
checked before publication. Principal declarations were transitively audited
using only propext, Classical.choice, and Quot.sound. Source-integrity and diff
checks passed. Every atomic mathematical commit was immediately pushed.
The twelve frozen prefix/identification source modules and their notes were not
modified.

Direct concrete nested reversal conjugation exceeded Lean's elaboration
recursion limit. A typed generic Hilbert conjugation lemma plus local
irreducibility of the two large full-space unitary definitions prevents
unnecessary unfolding; the kernel still checks the exact original definitions.
No resource limit, axiom, or kernel mechanism was changed.

A failed direct `change` tried to treat list append associativity as definitional
rather than propositional equality. An explicit ordered concatenation lemma
supplies the correct rewrite. Conditional tail-boundary simplification uses
typed operator applications to retain the intended letter labels.

## Next exact commutator obligation

The transported source-field result currently applies to the chosen full
source-basis fields. It does NOT yet imply the analogous result for an arbitrary
prescribed non-basis orthonormal family.

The next proposed exact identity is

[suffix(B), field(Vh)] = Γ(V) [B, field(h)] Γ(V).adjoint.

An unconditional CREATOR defect will be proved first on basis letters and
extended by the continuous complex-linear creator map and genuine full basis
expansions. Actual adjoints then give the annihilator defect and their sum gives
the real-field defect. The real field map itself is only real-linear in complex
h; applying complex-linear basis expansion directly to it would be invalid.
On the empty outside-head sector the commutator is the actual source
commutator; on nonempty heads it vanishes by coordinate independence. This is a
remaining proof target, not an assumed interface.

## Normal OU boundary

Literal double commutants, WOT-generated closures, and native norm closures
remain distinct. The suffix commutation interfaces may enable concrete rotated
compression double-commutant range arguments without a general Kaplansky theorem,
but that argument and a full normal OU extension are not achievements of these
modules. Infinite amplification is not globally WOT continuous on unbounded
nets; bounded-WOT and normality interfaces require their own precise proofs.
No entropy, hypercontractivity, or unproved von Neumann equivalence is claimed.

# Exact arbitrary-vector suffix defects and arbitrary-family commutants

## New verified creator-first chain

The earlier source-field commutant transport in fock-suffix-commutants.md was
correctly scoped to chosen source basis fields. The following five modules
resolve the arbitrary prescribed-family obligation without adding assumptions.

9fd86f9, SecondQuantizationSuffixDefectWords.lean, proves the unconditional
included right-creator commutator for actual prefix amplification. It equals
E_empty [T,rightCreation i] E_empty.adjoint, for EVERY bounded source T.
The adjoint of empty-tail inclusion selects exactly its complete orthogonal
sector. On every nonempty tail the creator action changes only the tail and
commutes with all prefix operators.

4ceda03, SecondQuantizationSuffixDefectReversal.lean, conjugates the literal
empty-tail sandwich through actual full-space reversal. Thus word suffix
amplification satisfies the unconditional LEFT creator defect, supported only
on the empty outside-head sector.

d7c5197, SecondQuantizationSuffixDefectTensor.lean, transports this operator
identity to the independently fixed completed tensor Fock spaces. A generic
unitary sandwich theorem plus the actual Γ(V) empty-sector identification gives

[suffix(T), creation(V b_i)] = Γ(V) [T, creation(b_i)] Γ(V).adjoint

for EVERY source basis vector b_i and EVERY bounded source operator T.

39a6281, SecondQuantizationSuffixDefectVectors.lean, extends that identity to
EVERY complex h in H. Both sides are actual norm-continuous COMPLEX-LINEAR
maps of h; the full Hilbert-basis HasSum therefore gives the all-vector equality.
The Γ sandwich is explicitly bundled as a continuous complex-linear operator
map and its actual adjoint compatibility is proved.

7938b23, SecondQuantizationSuffixDefectFields.lean, applies the creator identity
to star T, takes the actual Hilbert adjoint, and negates both sides to correct
the reversed commutator order. This gives the exact annihilator defect for all
h. Adding the two verified defects gives the literal real-field identity

[suffix(T), field(V h)] = Γ(V) [T, field(h)] Γ(V).adjoint.

No source commutation hypothesis is used in the defect identities. In
particular, commutation with ONE specified source field suffices for commutation
with its included field. `isometrySuffixEmbedding_commute_family_field` applies
to ANY prescribed e : I → H, without orthonormality, basis membership, spanning,
countability, or nontriviality assumptions. The earlier chosen-basis-only
limitation is thereby removed.

The real field map is only real-linear for complex h. Its complex-linear
extension was never assumed: the creator-first argument is essential, and the
actual adjoint supplies the conjugated coefficients of annihilation.

## Verification and implementation discoveries

All five final modules were compiled by focused Lake targets under the shared
lock with exit 0 explicitly checked BEFORE committing. Principal statements
passed direct transitive audits using only propext, Classical.choice, and
Quot.sound. Source-integrity and diff checks passed. Every atomic commit was
immediately pushed successfully. All frozen prefix, identification, and earlier
suffix modules and notes were left untouched.

Unitary coercions to bounded operators can have distinct elaboration metadata.
Explicit extensional coercion equalities reconcile the linear-isometry and
continuous-linear-equivalence routes before taking adjoints. Local
irreducibility of the large unitary and embedding definitions prevents recursive
rewrite search through their constructions; the kernel still checks the exact
original definitions. No proof resource limit or axiom changed.

Generic star-subtraction rewriting did not match the concrete operator metadata
in the annihilator proof. A typed generic adjoint-commutator lemma and explicit
adjoint involution equality resolve that elaboration issue and expose the
commutator sign correctly. No mathematical statement was weakened.

## Next literal double-commutant range dependency

Combined with the prior all-operator suffix Γ intertwining and all geometric
V-range-orthogonal creator/annihilator commutation, these exact field interfaces
supply the prerequisites for rotated compression range into the source literal
field double commutant. A source field-commutant B should have a suffix image
commuting with both included fields and the orthogonal noise fields, hence with
the real rotated fields. An operator in the rotated literal double commutant
then commutes with suffix(B), and Γ/adjoint intertwining transfers this to its
actual compression.

That range argument remains a separate proof target. Literal double commutants
are not identified with WOT-generated closures without a proved theorem.
Bounded-WOT continuity is the verified infinite-amplification interface; global
WOT continuity on unbounded nets is not used. Full normal OU extension,
all-bounded-operator semigroup laws, entropy, and hypercontractivity remain
separate obligations and are not conclusions of this checkpoint.

# Literal double-commutant amplification

The generic complete Hilbert-sum proof is published as `4367dae`. Actual matrix
blocks are eval_a Q single_b, bounded operators on the source. A target operator
commuting every amplified generator has each block in the source commutant.
An operator in the source double commutant commutes every block. Complete lp
continuous-linear-map extensionality promotes the single-coordinate identities
to all infinite vectors, proving actual amplification preserves double commutants.
The index set can be empty or arbitrary; no finite-support restriction is imposed.

`7d23481` transports this through the actual prefix/tail unitary and independently
fixed completed tensor Fock unitary. The generic multiplicative-equivalence
lemma needs only multiplication, without topology, star, or linearity. Initial
simp-only attempts at the homomorphism/equivalence projection and set-image eta
coherence failed; explicit function equality by extensionality and rfl, followed
by image_image, resolves this without resource changes or weakened statements.
`0b3c7fc` applies the actual field transport to every arbitrary family, proving
isometryPrefixEmbedding_mem_familyDoubleCentralizer. No ON assumption is needed.

These are literal Set.centralizer double commutants. Equality with WOT-generated
closures, positive-supremum normality, and a normal OU extension are not inferred.
The next range proof uses suffix representations of source commutant operators:
commutation with included fields and orthogonal-complement creators implies
commutation with rotated fields, and actual Gamma intertwining puts compression
into the original double commutant. This route avoids a general Kaplansky theorem
for range but still requires its own new kernel proofs.

An independent prospective all-operator semigroup argument uses uniformly bounded
finite word-rank compressions and bounded-WOT continuity. A normality interface
must prove actual directed bounded increasing-positive operator suprema; arbitrary
noncommuting operator sets need not possess suprema. Traciality on the double
commutant also remains separate: conjugate word reversal and full adapted right
Wick totality are the proposed coefficient-based route. None is a completed claim.

# Adversarial audit of the 1 August 2026 invalidity claim

**Status:** preliminary source-identification audit. The manuscript PDF was not
available to the automated reader, so this note evaluates only its public
abstract and does not purport to referee the full text.

On 1 August 2026, Jenny Lorraine Nielsen uploaded a rapidly revised PhilArchive
manuscript titled *Conne's Rigidity Theorem: Disproof of the Open AI and
Anthropic Counterexamples (with Proposed Proof of the Conjecture)*:

- <https://philarchive.org/rec/NIEWTC>

Its public abstract must be recorded because it directly disputes the status
statement in this repository. It does not, however, presently identify a flaw
in the constructions actually cited here.

## 1. Object mismatch

The abstract says that both alleged counterexamples are the same extension
construction involving

```text
Gamma_0 = Z^4 semidirect Sp_4(Z)
```

and a theta-characteristic Bockstein. The public OpenAI construction cited by
this repository instead uses binary divided powers over `F_2[t]`, a shifted
Witt carry, and an acting quotient `SL_4(F_2[t])`. Shuoxing Zhou's independent
construction uses a different binary rank-three action-shear mechanism. The
two public constructions are not the pair described in the abstract and are
not the same construction.

Thus a contradiction for the displayed `Z^4 semidirect Sp_4(Z)` pair would not
by itself refute either current paper.

## 2. Bernoulli-action inference gap

The abstract assumes an isomorphism of group factors and then chooses Bernoulli
actions for the two groups. It claims that twisted comultiplication and a
classification theorem produce an injective group homomorphism between the
groups.

An isomorphism

```text
L(Gamma_0) isomorphic to L(Gamma_1)
```

does not, by itself, identify crossed products coming from arbitrarily chosen
external Bernoulli actions. A theorem about rigidity of specified Bernoulli
crossed products needs hypotheses and an identification of those larger
crossed products; neither follows merely by adjoining actions after the group
factor isomorphism is assumed. The public abstract does not supply that bridge.

This is especially important here because the OpenAI carry proof gives the
group-factor isomorphism directly as the same represented crossed product

```text
L-infinity(X,mu) crossed-product Gamma,
```

where the measured action is fixed and only a compact abelian group law
changes. Any invalidity argument must attack that concrete Fourier/crossed-
product identification or one of the group-property inputs.

## 3. Current status label

The careful status statement is therefore:

> Two public papers claim counterexamples by distinct constructions. A very
> recent unreviewed manuscript disputes them, but its public abstract addresses
> different groups and contains an unfilled Bernoulli-action inference. It does
> not presently invalidate the cited counterexamples.

This repository should avoid both extremes: it should not suppress a current
adversarial claim, and it should not announce that a conjecture has been
restored on the basis of an abstract that does not match the mathematical
objects.

## 4. Required follow-up

1. Obtain and line-audit a stable manuscript version.
2. Identify the exact theorem claimed to turn a bare group-factor isomorphism
   into an isomorphism of chosen Bernoulli crossed products.
3. Compare every group definition against the official OpenAI chapter and
   Zhou's arXiv paper.
4. Ask an operator-algebra expert to referee the common-crossed-product step
   independently of all public commentary.

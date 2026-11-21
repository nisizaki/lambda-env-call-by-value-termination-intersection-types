# Call-by-Value Termination of λenv and its Characterization by Intersection Types

Isabelle/HOL formalization accompanying the paper

> Shin-ya Nishizaki and Shogo Murasaki.
> *Call-by-Value Termination of λenv and its Characterization by Intersection Types, Formalized in Isabelle/HOL.*

## Main result

For the calculus λenv with first-class environments, call-by-value reduction `→v` is
full σ-reduction together with a deterministic left-to-right β_v-reduction that fires only
when the argument is a *fireball* (a value or an inert term); environments are evaluated
lazily. For every raw term `M` (theory `Main_Results`):

```
theorem main_characterization:    "Typ M <-> CFN M"
theorem main_characterization_SN: "Typ M <-> CFSN M"
theorem Typ_imp_SN:               "Typ M ==> SN_at cbv M"
```

- `Typ M`: `M` has an essential type (a type not equivalent to ω) in the intersection
  type system with environment types; the system differs from the call-by-name one only
  in requiring the argument of an application to have an essential type.
- `CFN M`: `M` reduces to a normal form that is a fireball (clash-free).
- `CFSN M`: every `→v`-reduction sequence from `M` is finite and every normal form
  reachable from `M` is a fireball.

Further results:

- Evaluation-order independence (theory `Order_Independence`,
  `main_characterization_any_order`): `Typ M` holds iff every reduction sequence of σ
  together with nondeterministic β_v (arguments evaluated in any order) is finite and
  ends in a fireball.
- Conservativity (theory `Readback`, `conservativity`): for a pure λ-term `M`,
  `Typ M` holds iff its de Bruijn readback normalizes in left-to-right open
  call-by-value (the fireball calculus), iff `CFSN M`.
- Agreement with a classical call-by-value intersection type system (theories
  `VTypes`, `Classical`): in a system on de Bruijn λ-terms in the style of
  Ronchi Della Rocca and Paolini, where the type ν of values is given to abstractions
  by an axiom, a λ-term is typable iff it normalizes in open call-by-value
  (`classical_VN`); hence, for a pure `M`, `Typ M` holds iff the readback of `M` is
  typable in that system (`classical_agreement`).
- Uniqueness of normal forms (theory `Uniform`, `NF_unique`).

## Theories

The session `LambdaEnvCBV` consists of 16 theories (about 4,700 lines).

| Theory | Contents | Main results |
| --- | --- | --- |
| `ARS`, `Syntax` | abstract rewriting, terms; normal forms, SN | |
| `Sigma`, `Sig_Confluence` | σ-reduction, critical pairs, Newman's lemma | `sig_SN`, `sig_confluent` |
| `Reduction` | fireballs, β_v, call-by-value reduction | `beta_det` |
| `Uniform` | commutation, chains; weak and strong normalization coincide | `CFN_iff_CFSN`, `NF_unique` |
| `Typing` | types, subtyping, typing, generation lemmas | `narrowing`, `gen_*` |
| `Completeness` | subject expansion, refinement | `completeness` |
| `Soundness` | realizability interpretation, basic lemma | `soundness` |
| `Main_Results` | main theorem | `main_characterization`, `main_characterization_SN` |
| `Examples` | the examples of the paper | |
| `Order_Independence` | nondeterministic β_v, diamond, clashes | `main_characterization_any_order` |
| `Lambda`, `Readback` | de Bruijn λ-calculus, open call-by-value, readback | `conservativity` |
| `VTypes`, `Classical` | classical call-by-value intersection types | `classical_VN`, `classical_agreement` |

The theories contain no `sorry`, `oops`, `axiomatization`, `ML` code or other unchecked
declarations, and the session is built with `quick_and_dirty` and `skip_proofs`
disabled.

The σ-rules, their termination and confluence, the types, the subtyping and the
generation lemmas are shared, essentially unchanged, with the call-by-name development
(<https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types>);
this repository is self-contained and does not depend on it.

## Building

Requires [Isabelle2025-2](https://isabelle.in.tum.de/).

```bash
isabelle build -d isabelle LambdaEnvCBV
```

To also produce the theory documents (requires LaTeX):

```bash
isabelle build -o document=pdf -d isabelle LambdaEnvCBV
```

The output is written to `isabelle/output/`.

## File layout

```
isabelle/ROOT             session LambdaEnvCBV
isabelle/*.thy            the 16 theories
isabelle/document/root.tex
docs/document.pdf         theory document: all theories with proofs
docs/outline.pdf          theory document: all theories with proofs omitted
```

## Related repositories

- Lean 4 port of this development:
  <https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types-lean>
- Call-by-name (weak-head) counterpart (Isabelle/HOL):
  <https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types>,
  and its Lean 4 port:
  <https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types-lean>
- The same questions for λpenv:
  <https://github.com/nisizaki/lambda-penv-weak-head-normalizability-intersection-types>,
  <https://github.com/nisizaki/lambda-penv-call-by-value-termination-intersection-types>

## Authors

Shin-ya Nishizaki and Shogo Murasaki

## How to cite

Please cite the paper:

> Shin-ya Nishizaki and Shogo Murasaki.
> Call-by-Value Termination of λenv and its Characterization by Intersection Types,
> Formalized in Isabelle/HOL.

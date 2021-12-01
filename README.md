# Lean mathlib

![](https://github.com/leanprover-community/mathlib/workflows/continuous%20integration/badge.svg?branch=master)
[![Bors enabled](https://bors.tech/images/badge_small.svg)](https://app.bors.tech/repositories/24316)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://leanprover.zulipchat.com)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/leanprover-community/mathlib)

[Mathlib](https://leanprover-community.github.io) is a user maintained library for the [Lean theorem prover](https://leanprover.github.io).
It contains both programming infrastructure and mathematics,
as well as tactics that use the former and allow to develop the latter.

# Snake Lemma

Given commutative diagram
```
       A -----f-----> B  -----g-----> C ---> 0
       |              |               |
       α              β               γ
       |              |               |
       v              v               v
0 ---> A'-----f'----> B' -----g'----> C
```
Construct
```
ker α -> ker β -> ker γ --d--> coker α -> coker β -> coker γ
```

- [x] [φ  : ker α -> ker β](src/category_theory/abelian/diagram_lemmas/kernel.lean#L66)
- [x] [ψ  : ker β -> ker γ](src/category_theory/abelian/diagram_lemmas/kernel.lean#L67)
- [x] [exact φ ψ](src/category_theory/abelian/diagram_lemmas/kernel.lean#L114)
- [ ] d  : ker γ -> coker α
- [ ] φ' : coker α -> coker β
- [ ] exact d φ'
- [ ] ψ' : coker β -> coker γ
- [ ] exact φ' ψ'

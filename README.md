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
- [x] [d  : ker γ -> coker α ](src/category_theory/abelian/diagram_lemmas/snake.lean/#L95)
- [ ] exact ψ d
- [x] [φ'  : coker α -> coker β](src/category_theory/abelian/diagram_lemmas/kernel.lean#L194)
- [ ] exact d φ'
- [x] [ψ'  : coker β -> coker γ](src/category_theory/abelian/diagram_lemmas/kernel.lean#L195)
- [x] [exact φ' ψ'](src/category_theory/abelian/diagram_lemmas/kernel.lean#L225)


It turns out that snake lemma is part of liquid tensor experiment now, so this repo is archived.

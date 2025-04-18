### Commit Format
```
\d+(-\w+( \w+)*(
(OUTLINE|DEFINE|IMPLEMENT|PROVE|UPDATE|REFACTOR) \w+)*)? END
```

### Branch Format
```
\d+(-\w+(:\w+)*)?
```

# STAGE 1: THEORY

## Algebra

### Non-Annihilating Semirings
* Define `NonAnnihilatingSemiring` as a semiring with no annihilator
* Define `NonAnnihilatingCommSemiring` with commutativity
* Define `NonAnnihilatingIdemSemiring` and `NonAnnihilatingIdemCommSemiring` where addition is supremum
* Prove that these generate `Semiring`, `CommSemiring`, `IdemSemiring`, and `IdemCommSemiring` when given an annihilator

### Tropical Semirings
* Define `Antitropical` which induces a max-tropical semiring on a type
* Prove that these generate `NonAnnihilatingIdemSemiring` and `NonAnnihilatingIdemCommSemiring`

### Reordering Synonyms
* Create synonymous instances up to `IdemCommSemiring` for `Prod.Lex`
* Create synonymous instances up to `IdemCommSemiring` for `OrderDual`

## Automata

### List Enumeration
* Implement a `LinearOrder` for lists by length first then by elements
* Prove `WellFoundedLT` given it for elements
* Prove that the empty list is an `OrderBot`
* Implement a `SuccOrder` and `PredOrder` for lists given one for elements

### Machines
* Define `ListMachine` is a FSA with optional edges
* Define `CorrespondenceMachine` is a FST as a List Machine over products of options
* Implement `fold` over transition steps
* Implement `final` which returns the final state
* Implement `count` which counts transitions
* Prove that `count` is at most `length`

### Acceptance
* Define `collapse` which removes blanks from a correspondence
* Define `explode` as the preimage of collapse
* Define `explode_input`, `explode_output` as the preimage of collapse on just the input or output paired with any other list
* Prove decidability of `explode`
* Define `accept` as the set of accepting inputs from an initial state to a set of states
* Prove decidability of `accept`
* Define `accept_explode` as `accept` mapped by `collapse`

### Accept Enumeration
* Implement a `LinearOrder` and `WellFoundedLT` for accepted lists
* Prove that the next from the empty list is an `OrderBot`
* TODO: more detail on implementation
* Implement a `SuccOrder` and `PredOrder`
* Prove decidability of `accept_explode`

### Optimality
* Define `MachineWeights` assigning weights to all edges
* Define `cost` as the product of weights traversed by an input from an initial state
* Define `economy` mapping a set of inputs to a set of costs
* Define `harmonic_costs` and `harmonic_inputs` as the supremum cost of economy and the inputs yielding that cost

## Special Transducers

### Acceptors
* Implement `iacceptor`, `oacceptor` and its initial and final states
* TODO: probably something about fold
* Prove that `accept` is exactly `explode_input`, `explode_output`
* Prove that `accept_explode` is exactly lists with the fixed inputs or outputs

### Products
* Implement `prod` which produces a machine simulating two at once
* TODO: probably something about fold
* Prove that `accept` on the result is exactly the intersect of `accept` on the originals
* Prove that `accept_explode` on the result is exactly the intersect of `accept_explode` on the originals

### Optimality
* Implement  `prod_weights_with` which zips machine weight functions
* TODO: prove properties

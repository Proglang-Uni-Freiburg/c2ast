-*- agda2 -*-

# Title: 

1. regular session types with equirecursion: ST⁼

T ::= S | Unit | T ⊗ T | T → T
S ::= end! | end? | !T.S | ?T.S | ⊕{ l: S_l } | &{ l: S_l } | μX. S | X

All occurrences of μ in some S must be guarded / contractive:
There is no subterm of the form μX₁. μX₂. ⋯ μXₙ. X₁ (for n ≥ 1)

define: dual S

## Type equivalence  T ≈ᵗ T

Evidence for T₁ ≈ᵗ T₂ is an isomorphism (f, g) with f : T₁ → T₂ and g : T₂ → T₁.
We give just one half of the isomorphism, the other half being evident.

    λ x → x : Unit ≈ᵗ Unit

    f₁ : T₁ ≈ᵗ T₁′
    f₂ : T₂ ≈ᵗ T₂′
    --------------------
    λ p → let (x₁, x₂) = p in (f₁ x₁, f₂ x₂)
    : T₁ ⊗ T₂ ≈ᵗ T₁′ ⊗ T₂′

    f₁ : T₁ ≈ᵗ T₁′
    f₂ : T₂ ≈ᵗ T₂′
    --------------------
    λ p → f₂ ∘ p ∘ f₁⁻¹
    : T₁ → T₂ ≈ᵗ T₁′ → T₂′

    g : S₁ ≈ S₂
    -------------------------------------------
    λ c₁ → fork (λ (c₂ : dual S₂) → g (c₁, c₂))
    ;; λ c₂ → fork (λ (c₁ : dual S₁) → g⁻¹ (c₂, c₁))
    : S₁ ≈ᵗ S₂


## Session type equivalence  S ≈ˢ S

Evidence for (one direction of) S₁ ≈ S₂ is a process of type  (S₁, dual S₂) → Unit
(The other direction evidently omitted.)

λ (c₁ : end!, c₂ : end?) → let () = wait c₁ in terminate c₂
:
end! ≈ end!

f : T₁ ≈ᵗ T₂
g : S₁ ≈ˢ S₂
-----------------
λ (c₁ : ? T₁.S₁ , c₂ : ! T₂. dual S₂) → let (t₁, c₁) = receive c₁ in let c₂ = send c₂ (f t₁) in g (c₁, c₂)
:
? T₁.S₁ ≈ˢ ? T₂.S₂

(∀ l) g_l : S₁_l ≈ˢ S₂_l
----------------------------
λ (c₁,          c₂) →      case c₁ of { l: let c₂ = select l c2 in g_l (c₁, c₂) }
:
&{ l: S₁_l } ≈ˢ &{ l: S₂_l }

g : S₁[ μX.S₁ / X ] ≈ˢ S₂
--------------------
λ (c₁ : μX.S₁ , c₂ : dual S₂) → g (unroll c₁, c₂)
μX. S₁ ≈ˢ S₂

g : S₁ ≈ˢ S₂[ μX.S₂ / X ]
--------------------
λ (c₁ : S₁, c₂ : dual μX. S₂) → g (c₁, unroll c₂)
S₁ ≈ˢ μX. S₂

This is know to be constructive and gives rise to an algorithm.

## Examples

μX. !Int.X ≈ μX. !Int.X
----------------------------------------
!Int.μX. !Int.X ≈ !Int.μX. !Int.X         rec g₂ (c₁, c₂). let (t₁, c₁) = receive c₁ in let c₂ = send c₂ t₁ in g (c₁, c₂)
----------------------------------------
!Int.μX. !Int.X ≈ μX. !Int.X              rec g₁ (c₁, c₂). g₂ (c₁, unroll c₂)
----------------------------------------
μX. !Int.X ≈ μX. !Int.X                   rec g (c₁, c₂). g₁ (unroll c₁, c₂)

... unfolding yields:	rec g (c₁, c₂). let (t₁, c₁) = receive (unroll c₁) in let c₂ = send (unroll c₂) t₁ in g (c₁, c₂)

μX. !Int.X ≈ μX. !Int.!Int.X


μX. !Int.X ≈ μX. !Int.!Int.X
----------------------------------------
!Int.μX. !Int.X ≈ !Int. μX. !Int.!Int.X        rec g₄ (c₁, c₂). let (t₁, c₁) = receive c₁ in let c₂ = send c₂ t₁ in g (c₁, c₂)
----------------------------------------
μX. !Int.X ≈ !Int. μX. !Int.!Int.X             rec g₃ (c₁, c₂). g₄ (unroll c₁, c₂)
----------------------------------------
!Int.μX. !Int.X ≈ !Int.!Int. μX. !Int.!Int.X   rec g₂ (c₁, c₂). let (t₁, c₁) = receive c₁ in let c₂ = send c₂ t₁ in g₃ (c₁, c₂)
----------------------------------------
!Int.μX. !Int.X ≈ μX. !Int.!Int.X              rec g₁ (c₁, c₂). g₂ (c₁, unroll c₂)
----------------------------------------
μX. !Int.X ≈ μX. !Int.!Int.X                   rec g (c₁, c₂). g₁ (unroll c₁, c₂)

## Terms

M ::= x | λ x.M | M M | () | let () = M in M | (M, M) | let (x, y) = M in M
  | wait M | terminate M | send M M | receive M | select l M | case M of { l: M_l }

Standard conversion rule (applicable wherever)

Γ ⊢ M : T₁      T₁ ≈ᵗ T₂
-----------------------
Γ ⊢ M : T₂


## isorecursive version, ST≅


M ++= roll M | unroll M | fork M

Γ ⊢ M : S[ μX. S / X ]
----------------------
Γ ⊢ roll M : μX. S

Γ ⊢ M : μX. S
-----------------------------
Γ ⊢ unroll M : S[ μX. S / X ]

Γ ⊢ M : dual S → Unit
---------------------
Γ ⊢ fork M : S

## translation rule for conversion - all other translation rules are trivial

Γ ⊢ M ~> M′ : S₁
g : S₁ ≈ᵗ S₂
------------------------------------------------
Γ ⊢ M ~> g M′ : S₂

## normalized derivations (may no longer be needed)

### replace conversion with (iterated) top-level conversion: enough for wait, terminate, send, receive, select, case

Γ ⊢ M : μX. S
---------------------
Γ ⊢ M : S [μX. S / X]

### still need full conversion for arguments to functions and payload to send!

* the assumption was that `roll` and `unroll` give rise to synchronizing messages on the channel, but it seems like these messages can be avoided if the underlying recursive type is contractive:
* maybe we do not need to synchronize roll and unroll between client and server?
* suppose a channel configuration (c, d) has the invariant c : S and d : S' and S and S' are dual modulo roll/unroll
* at Send/Receive reduction, inversion yields c : !T.S and d : ?T'.S' where !T.S and !T'.S' are dual modulo roll/unroll
* but discrepancies between T and T' need to be resolved by applying a coercion and the same holds for function calls.
* (maybe we were too optimistic?)
* observation: when we look at the actual traffic on the wire, the conversions are nops: they just change the type, but have no operational effect.

## isorecursive → algebraic session types

This is a monadic function that returns a list of protocol types serving as argument list for a protocol constructor and
works over a writer monad that outputs a list of protocol definitions.
`new` generates a new name α for a protocol; so there has to be a name generation monad, too.
(we could get away with a reader over [Label], where `local f` applies f to the environment)

collect⟦_⟧ : (ReaderMonad [Label] m, WriterMonad [ProtocolDef] m) ⇒ IST → Map Var Name → m [ProtocolArg]

collect⟦ μX. S ⟧ ρ  = α ← new; output( protocol α = {α-roll: local (α-roll ∷) (collect⟦ S ⟧ ρ[X ↦ α])} ); return [+α]
collect⟦ X ⟧ ρ = return [+ ρ X]
collect⟦ !T.S ⟧ ρ = s ← collect⟦ S ⟧; return (+ T) ∷ s
collect⟦ ?T.S ⟧ ρ = s ← collect⟦ S ⟧; return (- T) ∷ s
collect⟦ !end ⟧ ρ = return [+ Unit]             ???
collect⟦ ?end ⟧ ρ = return [- Unit]             ???
collect⟦ ⊕{ l: S_l } ⟧ ρ = α ← new; output( protocol α = {l: local (l ∷) (collect⟦ S_l ⟧ ρ)} ); return [+ α]
collect⟦ &{ l: S_l } ⟧ ρ = α ← new; output( protocol α = {l: local (l ∷) (collect⟦ S_l ⟧ ρ)} ); return [- α]

### Translation of terms (sketch)

* unroll → select α-roll (requires the context of the type translation or protocols with overloaded constructors)
* roll → ???
* terminate → send ()
* wait → receive

### Wire compatibility

#### isorecursive setting

Given Δ : [ProtocolDef]
and   a : [ProtocolArg]
Define an LTS with transition relation

Δ ⊢ a →ᵐ a′

by

Δ ⊢ +T ∷ a →{!T} a
Δ ⊢ -T ∷ a →{?T} a
Δ ⊢ +α ∷ a →{!l} ca ++ a
  if Δ ∋ protocol α = {l: ca, ...}
Δ ⊢ -α ∷ a →{?l} -ca ++ a
  if Δ ∋ protocol α = {l: ca, ...}

Define an LTS for S : Session:

    S →ᵐ S′

holds if

    !T.S →{!T} S
    ?T.S →{?T} S
    ⊕{ l: S_l } →{!l} S_l
    &{ l: S_l } →{?l} S_l
    μX.S →{!μ-roll} S[μX.S / X]


Define S ≈ (a, Δ) as bisimulation:

* if S →ᵐ S′ then Δ ⊢ a →ᵐ a′ and S′ ≈ (a′, Δ)
* if Δ ⊢ a →ᵐ a′ then S →ᵐ S′ and S′ ≈ (a′, Δ)


Given S : Session
suppose
  collect⟦ S ⟧ ∅
return a and outputs Δ.
We have that S ≈ (a, Δ).

#### quasi equirecursive setting

* we assume that S : Session is contractive
* roll/unroll does not communicate
* tagging for protocols is optimized, such that non-recursive (needs proper definition inspired by contractiveness), single constructor protocols can omit their tag **if they are defined as transparent**

In the LTS for session types, we remove μ ­roll transitions and add silent transitions for unrolling:

    μX.S →τ S[μX.S / X]

In the LTS for algebraic session types,  we add silent transitions for transparent protocols:

    Δ ⊢ +α ∷ a →τ ca ++ a
      if Δ ∋ transparent protocol α = {l: ca}
    Δ ⊢ -α ∷ a →τ -ca ++ a
      if Δ ∋ transparent protocol α = {l: ca}

The translation collect⟦_⟧ changes such that branching is mapped to protocols and recursion is mapped to transparent protocols.
Bisimulation adapts correspondingly to weak bisimulation (I think).

#### wire compatibility for algebraic session types

Define (a, Δ) ≈ (a′, Δ′)
to obtain a relation between syntactically different algebraic session types which happen to have the same wire protocol.

NOW, we could extend the language with a cast between types a and a′ which has zero run time cost, but which may be expensive to check at compile time.
In particular the cast may have to invoke the decision procedure for CFST equivalence!



TODO: lift this notion to the equirecursive setting (using optimized tagging: no tag transmission for single constructor protocols unless they are directly recursive; maybe further refinement needed)
TODO: characterize the image of collect and define a backtranslation for such regular protocols
TODO: define notion of wire compatibility / bisimulation for regular protocols
  (so we have a notion of compatibility of algebraic session types different from equality)
  (so we can claim that a traditional session type and its translation to AlgSt are wire compatible)


----------------------------------------------------------------------
-- July 12, 2023
----------------------------------------------------------------------


Suppose

a ↝ a′ : End!
f : End! ↝ End!
---------------
a ↝ f a′ : End!

g : End! ↝ End!

f = λ c. fork (λ c′⊥ . g (c, c′⊥))

g = λ (c₁, c₂). wait c₂; term c₁

   a ↝ (λ c. fork (λ c′⊥ . (λ (c₁, c₂). wait c₂; term c₁) (c, c′⊥))) a′


   term a --term--> ()

   term ((λ c. fork (λ c′⊥ . (λ (c₁, c₂). wait c₂; term c₁) (c, c′⊥))) a′)
   —→
   term (fork (λ c′⊥ . (λ (c₁, c₂). wait c₂; term c₁) (a′, c′⊥)))
   —→
   (νab) (term a ∥ (λ c′⊥ . (λ (c₁, c₂). wait c₂; term c₁) (a′, c′⊥)) b)
   —→
   (νab) (term a ∥ (λ (c₁, c₂). wait c₂; term c₁) (a′, b))
   —→
   (νab) (term a ∥ (wait b; term a′))
   —→ (term∥wait)
   term a′
   
----------------------------------------------------------------------

    a ↝ a′ : !().End!
    f : !().End! ~ !().End!
    ---------------
    a ↝ f a′ : !().End!
    --------------------
    send v a ↝ send v (f a′) : End!

--a!v-->

    a ↝ a′ : End!
    f′ : End! ~ End!
    --------------------
    a ↝ f′ a′ : End!

0. e₁ →τ e₂ implies ⟦ e₁ ⟧ →* e₂′ and ⟦ e₂ ⟧ = e₂′
1. e₁ →α e₂ implies ⟦ e₁ ⟧ →*α* e₂′ and  ⟦ e₂ ⟧ ≡ e₂′ (or maybe   ⟦ e₂ ⟧ →* e₂' but seems too strong)
2. ⟦ e₁ ⟧ →*α e₁′  implies e₁ →α e₂ and ⟦ e₂ ⟧ ≡ e₁′ (equational correspondence)


Suppose

a ↝ a′ : !().End!
f : !().End! ~ !().End!
---------------
a ↝ f a′ : !().End!

g : !().End! ↝ !().End!

f = λ c. fork (λ c′⊥ . g₁ (c, c′⊥))
g₁ = λ (c₁, c₂). let (x, c₂) = recv c₂ in let c₁ = send f_()→() x c₁ in g₂ (c₁, c₂)
g₂ = λ (c₁, c₂). wait c₂; term c₁

  a ↝ λ c. fork (λ c′⊥ . (λ (c₁, c₂). let (x, c₂) = recv c₂ in let c₁ = send (f_()→() x) c₁ in (λ (c₁, c₂). wait c₂; term c₁) (c₁, c₂)) (c, c′⊥))

  send v a --(a!v)--> a₁

  send v (λ c. fork (λ c′⊥ . (λ (c₁, c₂). let (x, c₂) = recv c₂ in let c₁ = send (f_()→() x) c₁ in (λ (c₁, c₂). wait c₂; term c₁) (c₁, c₂)) (c, c′⊥))) a′
  —→
  send v (fork (λ c′⊥ . (λ (c₁, c₂). let (x, c₂) = recv c₂ in let c₁ = send (f_()→() x) c₁ in (λ (c₁, c₂). wait c₂; term c₁) (c₁, c₂)) (a′, c′⊥)))
  —→
  (νab) (send v a ∥ (λ (c₁, c₂). let (x, c₂) = recv c₂ in let c₁ = send (f_()→() x) c₁ in (λ (c₁, c₂). wait c₂; term c₁) (c₁, c₂)) (a′, b))
  —→
  (νab) (send v a ∥ let (x, b) = recv b in let a′ = send (f_()→() x) a′ in (λ (c₁, c₂). wait c₂; term c₁) (a′, b))
  —→ (send∥recv)
  (νab) (a ∥ let (x, b) = (v, b) in let a′ = send (f_()→() x) a′ in (λ (c₁, c₂). wait c₂; term c₁) (a′, b))
  —→ 
  (νab) (a ∥ let a′ = send (f_()→() v) a′ in (λ (c₁, c₂). wait c₂; term c₁) (a′, b))
  —→ 
  (νab) (a ∥ let a′ = send (f_()→() v) a′ in (λ (c₁, c₂). wait c₂; term c₁) (a′, b))
  —→* 
  (νab) (a ∥ let a′ = send v a′ in (λ (c₁, c₂). wait c₂; term c₁) (a′, b))
  --(a′!v)-->
  (νab) (a ∥ (λ (c₁, c₂). wait c₂; term c₁) (a′, b))
  —→
  (νab) (a ∥ (wait b; term a′))

Argument: (a, a′) ∈ V (End!) which means:

  (νab) (term a ∥ (wait b; term a′))
  ≡
  
----------------------------------------------------------------------

Attempting the equational correspondence for evaluation context

For evaluation context `case [] { lᵢ : eᵢ }` we do have a reduction correspondence.
For simplicity and wlog, I'd enforce that eᵢ is a value!

That is, we have a derivation ending in

    [ a : &{ lᵢ : S″ᵢ } ] ⊢ a ↝ a′ : &{ lᵢ : Sᵢ }
    f : &{ lᵢ : Sᵢ } ↝ &{ lᵢ : S′ᵢ }
    -----------------------------------
    [ a : &{ lᵢ : S″ᵢ } ] ⊢ a ↝ f a′ : &{ lᵢ : S′ᵢ }

f = λ c. fork (λ c′⊥ . g (c , c′⊥))
g = λ (c₁ , c₂). case c₁ { lᵢ : λ c₁ → let c₂ = sel lᵢ c₂ in gᵢ (c₁ , c₂) }
gᵢ = λ (c₁ , c₂). ⋯

* left side

    case a { lᵢ : eᵢ }
--a?lⱼ-->
    eⱼ a

* right side

    case (f a′) { lᵢ : eᵢ′ }
=
    case (fork (λ c′⊥ . g (a′ , c′⊥))) { lᵢ : eᵢ′ }
—→
    (νab) (case a { lᵢ : eᵢ′ } ∥ g (a′ , b))
=
    (νab) (case a { lᵢ : eᵢ′ } ∥ case a′ { lᵢ : λ c₁ → let c₂ = sel lᵢ b in gᵢ (c₁ , c₂) })
--a′?lⱼ-->
    (νab) (case a { lᵢ : eᵢ′ } ∥ let c₂ = sel lⱼ b in gⱼ (a′ , c₂))
-- τ = (a?lⱼ∥b!lⱼ) -->
    (νab) (eⱼ′ a ∥ gⱼ (a′ , b))

* typing after reduction

    [ a : S″ⱼ ] ⊢ a ↝ a′ : Sⱼ
    f : Sⱼ ↝ S′ⱼ
    -----------------------------------
    [ a : S″ᵢ ] ⊢ a ↝ f a′ : S′ⱼ

where

f = λ c. fork (λ c′⊥ . gⱼ (c , c′⊥))

* left side

    eⱼ a

* right side

    eⱼ′ (fork (λ c′⊥ . gⱼ (a′ , c′⊥)))
—→
    (νab) (eⱼ′ a ∥ gⱼ (a′ , b))

----------------------------------------------------------------------

For evaluation context `[] w`:

That is, we have a derivation ending in

    Γ ⊢ λx.e ↝ v′ : T → U
    f : T → U ↝ T′ → U′
    -----------------------------------
    Γ ⊢ λx.e ↝ f v′ : T′ → U′

where
    f : T → U ↝ T′ → U′
    <==
    f₁ : U ↝ U′
    f₂ : T′ ↝ T
and     
  f = λ h. λ x. f₁ (h (f₂ x))

* left side

    (λx.e) w
—→
    e[w/x]

* right side

    f (λx.e′) w
=
    (λ h. λ x. f₁ (h (f₂ x))) (λx.e′) w
—→
    (λ x. f₁ ((λx.e′) (f₂ x))) w
—→
    f₁ ((λx.e′) (f₂ w)))

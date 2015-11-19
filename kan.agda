{-# OPTIONS --type-in-type #-}

-- Inspired by Mark Bickford's Nuprl formalization of cubical sets

module kan where

module Cat where
  record t : Set where
    no-eta-equality
    field
      obj : Set
      hom : obj → obj → Set
      idn : {a : obj} → hom a a
      cmp : {a b c : obj} → hom b c → hom a b → hom a c

  open t public

  _ᵒᵖ : t → t
  𝒞 ᵒᵖ =
    record
      { obj = obj 𝒞
      ; hom = λ a b → hom 𝒞 b a
      ; idn = idn 𝒞
      ; cmp = λ γ δ → cmp 𝒞 δ γ
      }

module Sets where
  t : Set
  t = Set

  cat : Cat.t
  cat =
    record
      { obj = t
      ; hom = λ A B → A → B
      ; idn = λ {a} z → z
      ; cmp = λ {a} {b} {c} z z₁ z₂ → z (z₁ z₂)
      }

module Functor where
  record t (𝒞 𝒟 : Cat.t) : Set where
    no-eta-equality
    module 𝒞 = Cat.t 𝒞
    module 𝒟 = Cat.t 𝒟
    field
      obj : 𝒞.obj → 𝒟.obj
      hom : {a b : 𝒞.obj} → 𝒞.hom a b → 𝒟.hom (obj a) (obj b)

  open t public

module Presheaf where
  t : Cat.t → Set
  t 𝒞 = Functor.t (𝒞 ᵒᵖ) Sets.cat
    where
      open Cat

module RelativeMonad where
  record t {𝒞 𝒟 : Cat.t} (J : Functor.t 𝒞 𝒟) : Set where
    no-eta-equality
    module 𝒞 = Cat.t 𝒞
    module 𝒟 = Cat.t 𝒟
    module J = Functor.t J
    field
      T : 𝒞.obj → 𝒟.obj
      ret : {a : 𝒞.obj} → 𝒟.hom (J.obj a) (T a)
      bind : {a b : 𝒞.obj} → 𝒟.hom (J.obj a) (T b) → 𝒟.hom (T a) (T b)

  open t public

module 𝟘 where
  data t : Set where

module 𝟙 where
  record t : Set where
    constructor tt
  open t

module ∏ where
  _∘_ : {A : Set} {B : A -> Set} {C : (x : A) → B x → Set} (f : {x : A}(y : B x) → C x y)(g : (x : A) → B x) (x : A) → C x (g x)
  (f ∘ g) x = f (g x)

module ∐ where
  record t (A : Set) (B : A → Set) : Set where
    constructor _,_
    no-eta-equality
    field
      fst : A
      snd : B fst
  open t public

  syntax t A (λ x → B) = [ x ∶ A ] B

module ≡ where
  data _t_ {A : Set} (M : A) : A → Set where
    idn : M t M

  map
    : {A B : Set} {P : A → B} {M N : A}
    → M t N
    → P M t P N
  map idn = idn

  coe
    : {A B : Set}
    → A t B
    → A
    → B
  coe idn x = x

  _∘_ : {A : Set} {x y z : A} → y t z → x t y → x t z
  p ∘ idn = p

  injective : {A B : Set} (F : A → B) → Set
  injective F = {M N : _} → F M t F N → M t N

  cat : Set → Cat.t
  cat A =
    record
      { obj = A
      ; hom = _t_
      ; idn = idn
      ; cmp = _∘_
      }

  data Inspect {A : Set} (x : A) : Set where
    _with-≡_ : (y : A) (eq : x t y) → Inspect x

  inspect : {A : Set} (x : A) → Inspect x
  inspect x = x with-≡ idn


module ⊕ where
  data _t_ (A B : Set) : Set where
    inl : A → A t B
    inr : B → A t B

  inl-inj : {A B : Set} → ≡.injective (inl {A} {B})
  inl-inj ≡.idn = ≡.idn

  inr-inj : {A B : Set} → ≡.injective (inr {A} {B})
  inr-inj ≡.idn = ≡.idn

  ind
    : {A B : Set} (C : A t B → Set)
    → ((x : A) → C (inl x))
    → ((x : B) → C (inr x))
    → (x : A t B)
    → C x
  ind C l r (inl x) = l x
  ind C l r (inr x) = r x

  rec
    : {A B C : Set}
    → (A → C)
    → (B → C)
    → A t B
    → C
  rec l r (inl x) = l x
  rec l r (inr x) = r x

module Dec where
  t : Set → Set
  t A = A ⊕.t (A → 𝟘.t)

  pattern yes p = ⊕.inl p
  pattern no p = ⊕.inr p

  ≡ : Set → Set
  ≡ A =
    (M N : A)
      → t (M ≡.t N)


module ℕ where
  data t : Set where
    ze : t
    su : t → t

  {-# BUILTIN NATURAL t #-}

  su-inj : {M N : t} → su M ≡.t su N → M ≡.t N
  su-inj ≡.idn = ≡.idn

  dec-eq : Dec.≡ t
  dec-eq ze ze = Dec.yes ≡.idn
  dec-eq ze (su N) = Dec.no (λ ())
  dec-eq (su M) ze = Dec.no (λ ())
  dec-eq (su M) (su N) with dec-eq M N
  dec-eq (su M) (su .M) | Dec.yes ≡.idn = Dec.yes ≡.idn
  dec-eq (su M) (su N) | Dec.no p = Dec.no (λ q → p (su-inj q))

module Interval where
  data t : Set where
    #0 : t
    #1 : t

  dec-eq : Dec.≡ t
  dec-eq #0 #0 = Dec.yes ≡.idn
  dec-eq #0 #1 = Dec.no (λ ())
  dec-eq #1 #0 = Dec.no (λ ())
  dec-eq #1 #1 = Dec.yes ≡.idn

module Symbol where
  data t : Set where
    2+_ : ℕ.t → t

  2+-inj : {i j : ℕ.t} → (2+ i) ≡.t (2+ j) → i ≡.t j
  2+-inj ≡.idn = ≡.idn

  dec-eq : Dec.≡ t
  dec-eq (2+ x) (2+ y) with ℕ.dec-eq x y
  dec-eq (2+ x) (2+ y) | ⊕.inl p = Dec.yes (≡.map p)
  dec-eq (2+ x) (2+ y) | ⊕.inr p = Dec.no (λ q → p (2+-inj q))

module List where
  data t (A : Set) : Set where
    [] : t A
    _∷_ : A → t A → t A

  data ◇ {A : Set} (P : A → Set) : t A → Set where
    hd : {x : A} {xs : t A} → P x → ◇ P (x ∷ xs)
    tl : {x : A} {xs : t A} → ◇ P xs → ◇ P (x ∷ xs)

-- the cube category
module □ where
  ctx : Set
  ctx = List.t Symbol.t

  -- We have a functor ctx[≡] ⇒ Set which takes symbol contexts to their contents
  record t (I : ctx) : Set where
    no-eta-equality
    constructor ι[_]
    field
      π : Symbol.t
      .{∈} : List.◇ (≡._t π) I

  𝔉 : Functor.t (≡.cat ctx) Sets.cat
  𝔉 =
    record
      { obj = t
      ; hom = ≡.coe ∏.∘ ≡.map
      }

  module 𝔉 = Functor.t 𝔉

  module Ext where

    -- Next, we define a new functor ctx[≡] ⇒ Set that takes a symbol context to
    -- its contents ∪ {0,1}
    data ext (I : ctx) : Set where
      sym : t I → ext I
      dir : Interval.t → ext I

    sym-inj : {I : ctx} → ≡.injective (sym {I})
    sym-inj ≡.idn = ≡.idn

    data is-symbol {I : ctx} : ext I → Set where
      ✓-is-symbol : {i : t I} → is-symbol (sym i)

    -- ext is a relative monad on 𝔉; I don't recall this being observed in the CSM
    -- literature, but it seems like a pretty nice way to characterize what's going on.
    𝔐 : RelativeMonad.t 𝔉
    𝔐 =
      record
        { T = ext
        ; ret = sym
        ; bind = bind
        }
      where
        bind : {a b : ctx} → (t a → ext b) → ext a → ext b
        bind f (sym x) = f x
        bind f (dir x) = dir x

    module 𝔐 = RelativeMonad.t 𝔐

  record hom (I J : ctx) : Set where
    no-eta-equality
    constructor ι[_,_]
    field
      π : t I → Ext.ext J
      inj
        : (i j : t I) (open ∏)
        → Ext.is-symbol (π i)
        → Ext.is-symbol (π j)
        → (π i ≡.t π j → i ≡.t j)

  syntax hom I J = [ I , J ]

  idn : {I : ctx} → [ I , I ]
  idn =
    ι[ Ext.sym
     , (λ i j _ _ → Ext.sym-inj)
     ]

  cmp : {I J K : ctx} → [ J , K ] → [ I , J ] → [ I , K ]
  cmp J→K I→J =
    ι[ φ
     , φ-inj
     ]

    where
      φ : t _ → Ext.ext _
      φ = Ext.𝔐.bind (hom.π J→K) ∏.∘ hom.π I→J

      φ-inj : (i j : _) → Ext.is-symbol (φ i) → Ext.is-symbol (φ j) → φ i ≡.t φ j → i ≡.t j
      φ-inj i j pᵢ pⱼ q = {!!}

  open ∐ using (_,_)

  cat : Cat.t
  cat =
    record
      { obj = ctx
      ; hom = hom
      ; idn = idn
      ; cmp = cmp
      }


module cSet where
  t : Set
  t = Presheaf.t □.cat

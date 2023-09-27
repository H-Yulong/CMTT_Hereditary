module cmtt where

open import Agda.Primitive
open import Agda.Builtin.Sigma renaming (_,_ to _Σ,_)
open import Agda.Builtin.Bool

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)


infixl 5 _,_
infixl 5 _,,_
infixr 15 _⇒_
infix 10 [_]_⇒□_
infixl 10 _::[_]_
infixl 20 _∘_

_∘_ : {A : Set} {B : A → Set} {C : {x : A} → B x → Set}
      (f : {x : A}(y : B x) → C y) (g : (x : A) → B x) (x : A) → C (g x)
(f ∘ g) x = f (g x)

_+_ : Set → Set → Set
A + B = Σ Bool (λ {true -> A; false -> B})

inl : ∀{A B} → A → A + B
inl a = (true Σ, a)

inr : ∀{A B} → B → A + B
inr b = (false Σ, b)

subst : ∀{k l}{X : Set k}{s t : X} ->
  s ≡ t -> (P : X -> Set l) -> P s -> P t
subst refl P p = p

{-
  Summary (of things in this file)
  - Syntax of CMTT
  
  - Renamings for variables & meta-variables
  - Renamings & meta-renamings on terms
  
  - CPS-ed, single-variable substitution
  - Simultaneous substitution
  - CPS-ed, single-variable meta-substitution

  - Syntax of Neutral and Normal terms of CMTT
  
  - Renamings & meta-renamings on terms
  - Eta-expansion
  - Hereditary substitution algorithm

  - A few example terms

  There are many codes, but most of them are boilerplate.
-}

{- Syntax -}
mutual
  data Con : Set where
    ∙ : Con
    _,_ : Con → Ty → Con

  data Ty : Set where
    ι : Ty
    _⇒_ : Ty → Ty → Ty
    [_]_⇒□_ : Con → Ty → Ty → Ty

data MCon : Set where
  ∙ : MCon
  _::[_]_ : MCon → Con → Ty → MCon

data Var : Con → Ty → Set where
  vz : ∀{Γ α} → Var (Γ , α) α
  vs : ∀{Γ α β} → Var Γ α → Var (Γ , β) α
  
data MVar : MCon → Con → Ty → Set where
  mvz : ∀{𝓜 Γ α} → MVar (𝓜 ::[ Γ ] α) Γ α
  mvs : ∀{𝓜 Γ Δ α β} → MVar 𝓜 Γ α → MVar (𝓜 ::[ Δ ] β) Γ α

mutual 
  {- σ : Subst 𝓜 Γ Δ means that (𝓜 ; Γ ⊢ σ : Δ). -}
  data Subst : MCon → Con → Con → Set where
    ∙ : ∀{𝓜 Γ} → Subst 𝓜 Γ ∙
    _,_ : ∀{𝓜 Γ Δ α} → Subst 𝓜 Γ Δ → Tm 𝓜 Γ α → Subst 𝓜 Γ (Δ , α)

  data Tm : MCon → Con → Ty → Set where
    tt : ∀{𝓜 Γ} → Tm 𝓜 Γ ι
    var : ∀{𝓜 Γ α} → Var Γ α → Tm 𝓜 Γ α
    mvar : ∀{𝓜 Γ Δ α} → MVar 𝓜 Δ α → Subst 𝓜 Γ Δ → Tm 𝓜 Γ α
    lam : ∀{𝓜 Γ α β} → Tm 𝓜 (Γ , α) β → Tm 𝓜 Γ (α ⇒ β)
    app : ∀{𝓜 Γ α β} → Tm 𝓜 Γ (α ⇒ β) → Tm 𝓜 Γ α → Tm 𝓜 Γ β
    mlam : ∀{𝓜 Γ Δ α β} → Tm (𝓜 ::[ Δ ] α) Γ β → Tm 𝓜 Γ ([ Δ ] α ⇒□ β)
    mapp : ∀{𝓜 Γ Δ α β} → Tm 𝓜 Γ ([ Δ ] α ⇒□ β) → Tm 𝓜 Δ α → Tm 𝓜 Γ β

Sub : MCon → Con → Con → Set
Sub 𝓜 Γ Δ = ∀{α} → Var Γ α → Tm 𝓜 Δ α

interp-sub : ∀{𝓜 Γ Δ} → Subst 𝓜 Δ Γ → Sub 𝓜 Γ Δ   -- Notice the contravariance here
interp-sub (σ , t) vz = t
interp-sub (σ , t) (vs x) = interp-sub σ x

{- Renaming & Meta-renaming -}
Ren : Con → Con → Set
Ren Γ Δ = ∀{α} → Var Γ α → Var Δ α

MRen : MCon → MCon → Set
MRen 𝓜 𝓝 = ∀{Γ α} → MVar 𝓜 Γ α → MVar 𝓝 Γ α

-- MREn 𝓜 𝓝 = F (F[S] × S)

{- Their identity, weakening, and swap -}
idr : ∀{Γ} → Ren Γ Γ
idr x = x

wkr : ∀{Γ Δ α} → Ren Γ Δ → Ren (Γ , α) (Δ , α)
wkr ρ vz = vz
wkr ρ (vs x) = vs (ρ x)

sw : ∀{Γ β1 β2} → Ren (Γ , β1 , β2) (Γ , β2 , β1)
sw vz = vs vz
sw (vs vz) = vz
sw (vs (vs x)) = vs (vs x)

Midr : ∀{𝓜} → MRen 𝓜 𝓜
Midr 𝓍 = 𝓍

Mwkr : ∀{𝓜 𝓝 Γ α} → MRen 𝓜 𝓝 → MRen (𝓜 ::[ Γ ] α) (𝓝 ::[ Γ ] α)
Mwkr 𝓇 mvz = mvz
Mwkr 𝓇 (mvs 𝓍) = mvs (𝓇 𝓍) 

Msw : ∀{𝓜 Γ Δ α β} → MRen (𝓜 ::[ Γ ] α ::[ Δ ] β) (𝓜 ::[ Δ ] β ::[ Γ ] α)
Msw mvz = mvs mvz
Msw (mvs mvz) = mvz
Msw (mvs (mvs 𝓍)) = mvs (mvs 𝓍)

{- Renaming on terms & substitutions -}
mutual 
  ren-sub : ∀{𝓜 Γ Δ Ω} → Subst 𝓜 Γ Ω → Ren Γ Δ → Subst 𝓜 Δ Ω
  ren-sub ∙ ρ = ∙
  ren-sub (σ , t) ρ = (ren-sub σ ρ) , ren t ρ

  ren : ∀{𝓜 Γ Δ α} → Tm 𝓜 Γ α → Ren Γ Δ → Tm 𝓜 Δ α 
  ren tt ρ = tt
  ren (var x) ρ = var (ρ x)
  ren (mvar 𝓍 σ) ρ = mvar 𝓍 (ren-sub σ ρ)
  ren (lam t) ρ = lam (ren t (wkr ρ))
  ren (app s t) ρ = app (ren s ρ) (ren t ρ)
  ren (mlam t) ρ = mlam (ren t ρ)
  ren (mapp s t) ρ = mapp (ren s ρ) t     -- No renamings on t since it's closed

{- Meta-renaming on terms & substitutions -}

mutual
  Mren-sub : ∀{𝓜 𝓝 Γ Δ} → Subst 𝓜 Γ Δ → MRen 𝓜 𝓝 → Subst 𝓝 Γ Δ
  Mren-sub ∙ 𝓇 = ∙
  Mren-sub (σ , t) 𝓇 = Mren-sub σ 𝓇 , Mren t 𝓇

  Mren : ∀{𝓜 𝓝 Γ α} → Tm 𝓜 Γ α → MRen 𝓜 𝓝 → Tm 𝓝 Γ α
  Mren tt 𝓇 = tt
  Mren (var x) 𝓇 = var x
  Mren (mvar 𝓍 σ) 𝓇 = mvar (𝓇 𝓍) (Mren-sub σ 𝓇)
  Mren (lam t) 𝓇 = lam (Mren t 𝓇)
  Mren (app s t) 𝓇 = app (Mren s 𝓇) (Mren t 𝓇)
  Mren (mlam t) 𝓇 = mlam (Mren t (Mwkr 𝓇))
  Mren (mapp s t) 𝓇 = mapp (Mren s 𝓇) (Mren t 𝓇)


{- CPS-style single-variable substitution -}

mutual
  recsub-sub : ∀{𝓜 Γ Δ Ω β} → Subst 𝓜 Γ Ω → Ren Γ (Δ , β) → Tm 𝓜 Δ β → Subst 𝓜 Δ Ω
  recsub-sub ∙ ρ u = ∙
  recsub-sub (σ , t) ρ u = recsub-sub σ ρ u , recsub t ρ u

  recsub : ∀{𝓜 Γ Δ α β} → Tm 𝓜 Γ α → Ren Γ (Δ , β) → Tm 𝓜 Δ β → Tm 𝓜 Δ α
  recsub tt ρ u = tt
  recsub (var x) ρ u with ρ x
  ... | vz = u
  ... | vs x = var x
  recsub (mvar 𝓍 σ) ρ u = mvar 𝓍 (recsub-sub σ ρ u)
  recsub (lam t) ρ u = lam (recsub t (sw ∘ wkr ρ) (ren u vs))
  recsub (app s t) ρ u = app (recsub s ρ u) (recsub t ρ u)
  recsub (mlam t) ρ u = mlam (recsub t ρ (Mren u mvs))
  recsub (mapp s t) ρ u = mapp (recsub s ρ u) t

sub0 : ∀{𝓜 Γ α β} → Tm 𝓜 (Γ , β) α → Tm 𝓜 Γ β → Tm 𝓜 Γ α
sub0 t u = recsub t idr u

{- A few weakenings of substitutions -}
wks : ∀{𝓜 Γ Δ α} → Sub 𝓜 Γ Δ → Sub 𝓜 (Γ , α) (Δ , α)
wks σ vz = var vz
wks σ (vs x) = ren (σ x) vs

wkms : ∀{𝓜 Γ Δ Ω α} → Sub 𝓜 Γ Δ → Sub (𝓜 ::[ Ω ] α) Γ Δ
wkms σ x = Mren (σ  x) mvs

{- Simultaneous substitution -}
mutual
  _[_] :  ∀{𝓜 Γ Δ α} → Tm 𝓜 Γ α → Sub 𝓜 Γ Δ → Tm 𝓜 Δ α
  tt [ σ ] = tt
  var x [ σ ] = σ x
  mvar 𝓍 ρ [ σ ] = mvar 𝓍 (ρ < σ >)
  lam t [ σ ] = lam (t [ wks σ ])
  app s t [ σ ] = app (s [ σ ]) (t [ σ ])
  mlam t [ σ ] = mlam (t [ wkms σ ])
  mapp s t [ σ ] = mapp (s [ σ ]) t
  
  _<_> : ∀{𝓜 Γ Δ Ω} → Subst 𝓜 Γ Ω → Sub 𝓜 Γ Δ → Subst 𝓜 Δ Ω
  ∙ < σ > = ∙
  (ρ , t) < σ > = (ρ < σ >) , (t [ σ ])

{- CPS-style single-variable meta-substitution -}
mutual
  Mrecsub-sub : ∀{𝓜 𝓝 Γ Δ Ω β} → 
    Subst 𝓜 Γ Ω → MRen 𝓜 (𝓝 ::[ Δ ] β) → Tm 𝓝 Δ β → Subst 𝓝 Γ Ω
  Mrecsub-sub ∙ 𝓇 u = ∙
  Mrecsub-sub (σ , t) 𝓇 u = Mrecsub-sub σ 𝓇 u , Mrecsub t 𝓇 u

  Mrecsub : ∀{𝓜 𝓝 Γ Δ α β} → 
    Tm 𝓜 Γ α → MRen 𝓜 (𝓝 ::[ Δ ] β) → Tm 𝓝 Δ β → Tm 𝓝 Γ α
  Mrecsub tt 𝓇 u = tt
  Mrecsub (var x) 𝓇 u = var x
  Mrecsub (mvar 𝓍 σ) 𝓇 u with 𝓇 𝓍
  -- Need simultaneous substitution here
  ... | mvz = u [ interp-sub (Mrecsub-sub σ 𝓇 u) ]
  ... | mvs 𝓍 = mvar 𝓍 (Mrecsub-sub σ 𝓇 u)
  Mrecsub (lam t) 𝓇 u = lam (Mrecsub t 𝓇 u)
  Mrecsub (app s t) 𝓇 u = app (Mrecsub s 𝓇 u) (Mrecsub t 𝓇 u)
  Mrecsub (mlam t) 𝓇 u = mlam (Mrecsub t (Msw ∘ Mwkr 𝓇) (Mren u mvs))
  Mrecsub (mapp s t) 𝓇 u = mapp (Mrecsub s 𝓇 u) (Mrecsub t 𝓇 u)

{- Helper definitions for simultaneous substituttion -}

_^_ : Con → Con → Con
Δ ^ ∙ = Δ
Δ ^ (Γ , x) = (Δ ^ Γ) , x

id^ : ∀{Γ} → Γ ≡ ∙ ^ Γ
id^ {∙} = refl
id^ {Γ , x} = cong (λ Γ → Γ , x) id^

l^ : {Γ : Con} → {Δ : Con} → Ren Γ (Δ ^ Γ)
l^ {Γ} {∙} {α} x = subst id^ (λ Γ → Var Γ α) x
l^ {Γ} {Δ , _} vz = vz
l^ {Γ} {Δ , _} (vs x) = vs (l^ x)

r^ : ∀{Γ Δ} → Ren Γ (Γ ^ Δ)
r^ {Γ} {∙} x = x
r^ {Γ} {Δ , _} x = vs (r^ x)

{- Neutral, Normal, Spine -}
mutual  
  data Nf : MCon → Con → Ty → Set where
    tt : ∀{𝓜 Γ} → Nf 𝓜 Γ ι
    neu : ∀{𝓜 Γ} → Ne 𝓜 Γ ι → Nf 𝓜 Γ ι
    lam : ∀{𝓜 Γ α β} → Nf 𝓜 (Γ , α) β → Nf 𝓜 Γ (α ⇒ β)
    mlam : ∀{𝓜 Γ Δ α β} → Nf (𝓜 ::[ Δ ] α) Γ β → Nf 𝓜 Γ ([ Δ ] α ⇒□ β)

  data Ne : MCon → Con → Ty → Set where
    _,_ : ∀{𝓜 Γ α β} → Var Γ α → Sp 𝓜 Γ α β → Ne 𝓜 Γ β
    mvar : ∀{𝓜 Γ Δ α β} → MVar 𝓜 Δ α → NSubst 𝓜 Γ Δ → Sp 𝓜 Γ α β → Ne 𝓜 Γ β

  data Sp : MCon → Con → Ty → Ty → Set where
    ∙ : ∀{𝓜 Γ α} → Sp 𝓜 Γ α α
    _,_ : ∀{𝓜 Γ α₁ α₂ β} → Nf 𝓜 Γ α₁ → Sp 𝓜 Γ α₂ β → Sp 𝓜 Γ (α₁ ⇒ α₂) β
    _,,_ : ∀{𝓜 Γ Δ α₁ α₂ β} → Nf 𝓜 Δ α₁ → Sp 𝓜 Γ α₂ β → Sp 𝓜 Γ ([ Δ ] α₁ ⇒□ α₂) β

  data NSubst : MCon → Con → Con → Set where
    ∙ : ∀{𝓜 Γ} → NSubst 𝓜 Γ ∙
    _,_ : ∀{𝓜 Γ Δ α} → NSubst 𝓜 Γ Δ → Nf 𝓜 Γ α → NSubst 𝓜 Γ (Δ , α)
    _,,_ : ∀{𝓜 Γ Δ α} → NSubst 𝓜 Γ Δ → Ne 𝓜 Γ α → NSubst 𝓜 Γ (Δ , α)


{- Renamings on Nf, Ne, Sp -}
mutual
  renNf : ∀{𝓜 Γ Δ α} → Nf 𝓜 Γ α → Ren Γ Δ → Nf 𝓜 Δ α
  renNf tt ρ = tt
  renNf (neu u) ρ = neu (renNe u ρ)
  renNf (lam t) ρ = lam (renNf t (wkr ρ))
  renNf (mlam t) ρ = mlam (renNf t ρ)

  renNe : ∀{𝓜 Γ Δ α} → Ne 𝓜 Γ α → Ren Γ Δ → Ne 𝓜 Δ α
  renNe (x , sp) ρ = ρ x , renSp sp ρ
  renNe (mvar 𝓍 σ sp) ρ = mvar 𝓍 (renNSub σ ρ) (renSp sp ρ)

  renSp : ∀{𝓜 Γ Δ α β} → Sp 𝓜 Γ α β → Ren Γ Δ → Sp 𝓜 Δ α β
  renSp ∙ ρ = ∙
  renSp (t , sp) ρ = renNf t ρ , renSp sp ρ
  renSp (t ,, sp) ρ = t ,, renSp sp ρ

  renNSub : ∀{𝓜 Γ Δ Ω} → NSubst 𝓜 Γ Ω → Ren Γ Δ → NSubst 𝓜 Δ Ω 
  renNSub ∙ ρ = ∙
  renNSub (σ , t) ρ = renNSub σ ρ , renNf t ρ
  renNSub (σ ,, t) ρ = renNSub σ ρ ,, renNe t ρ


mutual
  MrenNf : ∀{𝓜 𝓝 Γ α} → Nf 𝓜 Γ α → MRen 𝓜 𝓝 → Nf 𝓝 Γ α
  MrenNf tt 𝓇 = tt
  MrenNf (neu u) 𝓇 = neu (MrenNe u 𝓇)
  MrenNf (lam t) 𝓇 = lam (MrenNf t 𝓇)
  MrenNf (mlam t) 𝓇 = mlam (MrenNf t (Mwkr 𝓇))

  MrenNe : ∀{𝓜 𝓝 Γ α} → Ne 𝓜 Γ α → MRen 𝓜 𝓝 → Ne 𝓝 Γ α
  MrenNe (x , sp) 𝓇 = x , MrenSp sp 𝓇
  MrenNe (mvar 𝓍 σ sp) 𝓇 = mvar (𝓇 𝓍) (MrenNSub σ 𝓇) (MrenSp sp 𝓇)

  MrenSp : ∀{𝓜 𝓝 Γ α β} → Sp 𝓜 Γ α β → MRen 𝓜 𝓝 → Sp 𝓝 Γ α β
  MrenSp ∙ 𝓇 = ∙
  MrenSp (t , sp) 𝓇 = MrenNf t 𝓇 , MrenSp sp 𝓇
  MrenSp (t ,, sp) 𝓇 = MrenNf t 𝓇 ,, MrenSp sp 𝓇

  MrenNSub : ∀{𝓜 𝓝 Γ Δ} → NSubst 𝓜 Γ Δ → MRen 𝓜 𝓝 → NSubst 𝓝 Γ Δ
  MrenNSub ∙ 𝓇 = ∙
  MrenNSub (σ , t) 𝓇 = MrenNSub σ 𝓇 , MrenNf t 𝓇
  MrenNSub (σ ,, t) 𝓇 = MrenNSub σ 𝓇 ,, MrenNe t 𝓇

{- A bunch of different weakenings -}
wkst : ∀{Γ Δ 𝓜 α} → NSubst 𝓜 Γ Δ → NSubst 𝓜 (Γ , α) Δ
wkst ∙ = ∙
wkst (σ , x) = wkst σ , renNf x vs
wkst (σ ,, x) = wkst σ ,, renNe x vs

Mwkst : ∀{Γ Δ Ω 𝓜 α} → NSubst 𝓜 Γ Δ → NSubst (𝓜 ::[ Ω ] α) Γ Δ
Mwkst ∙ = ∙
Mwkst (σ , x) = Mwkst σ , MrenNf x mvs
Mwkst (σ ,, x) = Mwkst σ ,, MrenNe x mvs

wkSp : ∀{𝓜 Γ α β γ} → Sp 𝓜 Γ α β → Sp 𝓜 (Γ , γ) α β
wkSp sp = renSp sp vs

MwkSp : ∀{𝓜 Γ Δ α β γ} → Sp 𝓜 Γ α β → Sp (𝓜 ::[ Δ ] γ) Γ α β
MwkSp sp = MrenSp sp mvs

{- Identity substitution -}
ids : ∀{Γ 𝓜} → NSubst 𝓜 Γ Γ
ids {∙} = ∙
ids {Γ , α} = wkst ids ,, (vz , ∙)

{- Appending an element to a spine -}
appSp : ∀{Γ 𝓜 α β γ} → Sp 𝓜 Γ γ (α ⇒ β) → Nf 𝓜 Γ α → Sp 𝓜 Γ γ β
appSp ∙ t = t , ∙
appSp (x , sp) t = x , appSp sp t
appSp (x ,, sp) t = x ,, appSp sp t

appSp□ : ∀{Γ Δ 𝓜 α β γ} → Sp 𝓜 Γ γ ([ Δ ] α ⇒□ β) → Nf 𝓜 Δ α → Sp 𝓜 Γ γ β 
appSp□ ∙ t = t ,, ∙
appSp□ (x , sp) t = x , appSp□ sp t
appSp□ (x ,, sp) t = x ,, appSp□ sp t

Nget : ∀{𝓜 Γ Δ α} → NSubst 𝓜 Γ Δ → Var Δ α → (Nf 𝓜 Γ α + Ne 𝓜 Γ α)
Nget (σ , x) vz = inl x
Nget (σ ,, x) vz = inr x
Nget (σ , x₁) (vs x) = Nget σ x
Nget (σ ,, x₁) (vs x) = Nget σ x


{- Joining two spines -}
_++_ : ∀{Γ 𝓜 α β γ} → Sp 𝓜 Γ α β → Sp 𝓜 Γ β γ → Sp 𝓜 Γ α γ
∙ ++ sp' = sp'
(x , sp) ++ sp' = x , sp ++ sp'
(x ,, sp) ++ sp' = x ,, sp ++ sp'

{- Normalization -}

{- Eta-expansions -}
mutual
  ηvar : ∀{Γ 𝓜 α} → Var Γ α → Nf 𝓜 Γ α
  ηvar x = ne2nf (x , ∙)

  ηmvar : ∀{Γ Δ 𝓜 α} → MVar 𝓜 Δ α → NSubst 𝓜 Γ Δ → Nf 𝓜 Γ α
  ηmvar 𝓍 σ = ne2nf (mvar 𝓍 σ ∙)

  {- Keep pushing η-expanded vars/meta-vars to the end of the spine -}
  ne2nf : ∀{Γ 𝓜 α} → Ne 𝓜 Γ α → Nf 𝓜 Γ α
  ne2nf {α = ι} u = neu u
  ne2nf {α = α ⇒ β} (x , sp) = lam (ne2nf (vs x , appSp (wkSp sp) (ηvar vz)))
  ne2nf {α = α ⇒ β} (mvar 𝓍 σ sp) = lam (ne2nf (mvar 𝓍 (wkst σ) (appSp (wkSp sp) (ηvar vz))))
  -- ⊢ x ≡η λ□ u:[Δ]A ⇒□ B. x (Δ. u[id])  : [Δ]A ⇒□ B
  ne2nf {α = [ Δ ] α ⇒□ β} (x , sp) = mlam (ne2nf (x , appSp□ (MwkSp sp) (ηmvar mvz ids)))
  ne2nf {α = [ Δ ] α ⇒□ β} (mvar 𝓍 σ sp) = mlam (ne2nf (mvar (mvs 𝓍) (Mwkst σ) (appSp□ (MwkSp sp) (ηmvar mvz ids))))

{- 
  Now, for hereditary substitution, we need the following three substitutions,
  for (Nf, Sp, NSubst) respectively:
    single-variable substitution  _[_,_]0  _<_,_>0  _[_,_]s
    simultaneous substitution     _[_]sim  _<_>sim  _[_]sim-s
    single-var meta-substitution  _⟦_,_⟧0  _⟪_,_⟫0   _⟦_,_⟧s
-}

_[_,_]0    : ∀{Γ Δ 𝓜 α β} → Nf 𝓜 Γ α → Ren Γ (Δ , β) → Nf 𝓜 Δ β → Nf 𝓜 Δ α
_<_,_>0    : ∀{Γ Δ 𝓜 α β γ} → Sp 𝓜 Γ α γ → Ren Γ (Δ , β) → Nf 𝓜 Δ β → Sp 𝓜 Δ α γ
_[_,_]s    : ∀{Γ Δ Ω 𝓜 β} → NSubst 𝓜 Γ Ω → Ren Γ (Δ , β) → Nf 𝓜 Δ β → NSubst 𝓜 Δ Ω

sub-aux    : ∀{Γ Δ 𝓜 α} → Nf 𝓜 (Γ ^ Δ) α → NSubst 𝓜 Γ Δ → Nf 𝓜 Γ α
_[_]sim    : ∀{Γ Δ 𝓜 α} → Nf 𝓜 Δ α → NSubst 𝓜 Γ Δ → Nf 𝓜 Γ α
_<_>sim    : ∀{Γ Δ 𝓜 α β} → Sp 𝓜 Δ α β → NSubst 𝓜 Γ Δ → Sp 𝓜 Γ α β
_[_]sim-s  : ∀{Γ Δ Ω 𝓜} → NSubst 𝓜 Γ Δ → NSubst 𝓜 Ω Γ → NSubst 𝓜 Ω Δ

_⟦_,_⟧0    : ∀{Γ Δ 𝓜 𝓝 α β} → Nf 𝓜 Γ α → MRen 𝓜 (𝓝 ::[ Δ ] β) → Nf 𝓝 Δ β → Nf 𝓝 Γ α
_⟪_,_⟫0   : ∀{Γ Δ 𝓜 𝓝 α β γ} → Sp 𝓜 Γ α γ → MRen 𝓜 (𝓝 ::[ Δ ] β) → Nf 𝓝 Δ β → Sp 𝓝 Γ α γ
_⟦_,_⟧s    : ∀{Γ Δ Ω 𝓜 𝓝 β} → NSubst 𝓜 Γ Ω → MRen 𝓜 (𝓝 ::[ Δ ] β) → Nf 𝓝 Δ β → NSubst 𝓝 Γ Ω

_$_ : ∀{Γ 𝓜 α β} → Nf 𝓜 Γ α → Sp 𝓜 Γ α β → Nf 𝓜 Γ β
napp : ∀{Γ 𝓜 α β} → Nf 𝓜 Γ (α ⇒ β) → Nf 𝓜 Γ α → Nf 𝓜 Γ β
nmapp : ∀{Γ Δ 𝓜 α β} → Nf 𝓜 Γ ([ Δ ] α ⇒□ β) → Nf 𝓜 Δ α → Nf 𝓜 Γ β

-------------- Single variable substitutions

tt [ ρ , u ]0 = tt
neu (x , sp) [ ρ , u ]0 with ρ x
... | vz = u $ (sp < ρ , u >0)
... | vs y = neu (y , sp < ρ , u >0)
neu (mvar 𝓍 σ sp) [ ρ , u ]0 = neu (mvar 𝓍 (σ [ ρ , u ]s) (sp < ρ , u >0))
lam t [ ρ , u ]0 = lam (t [ sw ∘ wkr ρ , renNf u vs ]0)
mlam t [ ρ , u ]0 = mlam (t [ ρ , MrenNf u mvs ]0)

∙ < ρ , u >0 = ∙
(t , sp) < ρ , u >0 = t [ ρ , u ]0 , sp < ρ , u >0
(t ,, sp) < ρ , u >0 = t ,, (sp < ρ , u >0)

∙ [ ρ , u ]s = ∙
(σ , x) [ ρ , u ]s = σ [ ρ , u ]s , x [ ρ , u ]0
(σ ,, (x , sp)) [ ρ , u ]s with ρ x
... | vz = σ [ ρ , u ]s , (u $ (sp < ρ , u >0))
... | vs y = σ [ ρ , u ]s ,, (y , (sp < ρ , u >0))
(σ ,, mvar 𝓍 π sp) [ ρ , u ]s = σ [ ρ , u ]s ,, mvar 𝓍 (π [ ρ , u ]s) (sp < ρ , u >0)

-------------- Simultaneous substitutions

sub-aux {Δ = ∙} t [] = t
sub-aux {Δ = Δ , x} t (σ , u) = sub-aux (t [ idr , renNf u r^ ]0) σ
sub-aux {Δ = Δ , x} t (σ ,, u) = sub-aux (t [ idr , ne2nf (renNe u r^) ]0) σ

t [ σ ]sim = sub-aux (renNf t l^) σ

∙ < σ >sim = ∙
(t , sp) < σ >sim = t [ σ ]sim , sp < σ >sim
(t ,, sp) < σ >sim = t ,, sp < σ >sim

∙ [ σ ]sim-s = ∙
(π , x) [ σ ]sim-s = π [ σ ]sim-s , x [ σ ]sim
(π ,, (x , sp)) [ σ ]sim-s with Nget σ x
... | false Σ, x , sp' = π [ σ ]sim-s ,, (x , (sp' ++ (sp < σ >sim)))
... | false Σ, mvar 𝓍 τ sp' = (π [ σ ]sim-s) ,, mvar 𝓍 τ (sp' ++ (sp < σ >sim))
... | true Σ, t = π [ σ ]sim-s , (t $ (sp < σ >sim))
(π ,, mvar 𝓍 τ sp) [ σ ]sim-s = π [ σ ]sim-s ,, mvar 𝓍 (τ [ σ ]sim-s) (sp < σ >sim)

-------------- Meta-substitutions

tt ⟦ 𝓇 , u ⟧0 = tt
neu (x , sp) ⟦ 𝓇 , u ⟧0 = neu (x , sp ⟪ 𝓇 , u ⟫0)
neu (mvar 𝓍 σ sp) ⟦ 𝓇 , u ⟧0 with 𝓇 𝓍
... | mvz = (u [ σ ⟦ 𝓇 , u ⟧s ]sim) $ (sp ⟪ 𝓇 , u ⟫0)     
... | mvs 𝓎 = neu (mvar 𝓎 (σ ⟦ 𝓇 , u ⟧s) (sp ⟪ 𝓇 , u ⟫0))
lam t ⟦ 𝓇 , u ⟧0 = lam (t ⟦ 𝓇 , u ⟧0)
mlam t ⟦ 𝓇 , u ⟧0 = mlam (t ⟦ Msw ∘ Mwkr 𝓇 , MrenNf u mvs ⟧0)

∙ ⟪ 𝓇 , u ⟫0 = ∙
(t , sp) ⟪ 𝓇 , u ⟫0 = t ⟦ 𝓇 , u ⟧0 , sp ⟪ 𝓇 , u ⟫0
(t ,, sp) ⟪ 𝓇 , u ⟫0 = t ⟦ 𝓇 , u ⟧0 ,, sp ⟪ 𝓇 , u ⟫0 

∙ ⟦ 𝓇 , u ⟧s = ∙
(σ , x) ⟦ 𝓇 , u ⟧s = σ ⟦ 𝓇 , u ⟧s , x ⟦ 𝓇 , u ⟧0
(σ ,, (x , sp)) ⟦ 𝓇 , u ⟧s = σ ⟦ 𝓇 , u ⟧s ,, (x , (sp ⟪ 𝓇 , u ⟫0))
(σ ,, mvar 𝓍 π sp) ⟦ 𝓇 , u ⟧s with 𝓇 𝓍
... | mvz = σ ⟦ 𝓇 , u ⟧s , ((u [ π ⟦ 𝓇 , u ⟧s ]sim) $ (sp ⟪ 𝓇 , u ⟫0))
... | mvs 𝓎 = σ ⟦ 𝓇 , u ⟧s ,, mvar 𝓎 (π ⟦ 𝓇 , u ⟧s) (sp ⟪ 𝓇 , u ⟫0)

-------------- Applications

t $ ∙ = t
t $ (x , sp) = (napp t x) $ sp
t $ (x ,, sp) = (nmapp t x) $ sp

napp (lam t) u = t [ idr , u ]0

nmapp (mlam t) u = t ⟦ Midr , u ⟧0

-------------- 

mutual
  nf-sub : ∀{𝓜 Γ Δ} → Subst 𝓜 Γ Δ → NSubst 𝓜 Γ Δ
  nf-sub ∙ = ∙
  nf-sub (σ , x) = nf-sub σ , nf x

  nf : ∀{𝓜 Γ α} → Tm 𝓜 Γ α → Nf 𝓜 Γ α
  nf tt = tt
  nf (var x) = ηvar x
  nf (mvar x σ) = ηmvar x (nf-sub σ)
  nf (lam t) = lam (nf t)
  nf (app s t) = napp (nf s) (nf t)
  nf (mlam t) = mlam (nf t)
  nf (mapp s t) = nmapp (nf s) (nf t)


{- Example terms -} 
A B C : Ty
A = ι ⇒ ι
B = [ ∙ ] ι ⇒□ ι
C = [ ∙ ] ι ⇒□ ι ⇒ ι

t1 : Tm ∙ ∙ (([ ∙ , C ] A ⇒□ B) ⇒ ([ ∙ , C , C ] A ⇒□ B))
t1 = lam (mlam (mapp (var vz) (mvar mvz (∙ , (var vz) , (var vz)))))

t2 : Tm ∙ ∙ (([ ∙ , A ] B ⇒□ C) ⇒ ([ ∙ ] (A ⇒ B) ⇒□ C))
t2 = lam (mlam (mapp (var vz) (app (mvar mvz ∙) (var vz))))

-- Test η-expansion
t3 : Var (∙ , [ ∙ , ι ] ι ⇒□ ι ⇒ ι) ([ ∙ , ι ] ι ⇒□ ι ⇒ ι)
t3 = vz

  
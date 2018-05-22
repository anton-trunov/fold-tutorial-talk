(** Imports and settings *)

From Coq Require Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From Equations Require Import Equations Subterm.
Set Implicit Arguments.
Set Equations Transparent.


(** Preliminaries *)

(* redefining [list] for the sake of making a self-contained example *)
Inductive list (α : Type) : Type :=
  | nil : list α
  | cons (head : α) (tail : list α) : list α.

Arguments nil {α}.
Arguments cons {α} head tail.

Notation "(::)" := (cons).
Infix "::" := cons (at level 60, right associativity).
Notation "[ ]" := (nil) (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)).

Notation "(∘)" := comp.
Notation "f ∘ g" := (comp f g).
Definition flip {α β γ} (f : α -> β -> γ) := λ x y, f y x.
Definition fsplice {α β γ} (f : α -> β) (g : α -> γ) :=
  [fun x => (f x, g x)].
Notation "[ 'fs' f , g ]" := (fsplice f g).

(* "sections" a-la Haskell *)
Notation "(+1)" := (S).
Notation "(+)" := (Nat.add).
Notation "x + y" := (Nat.add x y).
Notation "(×)" := (Nat.mul).
Notation "(&&)" := (andb).
Notation "(||)" := (orb).


(** Some functions implemented via fold *)

Equations fold {α β} (f : α -> β -> β) (v : β) (xs : list α) : β :=
fold f v []            := v ;
fold f v (cons h tail) := f h (fold f v tail).

Definition sum :=
  [fun xs => fold (+) 0 xs].

Definition and : list bool -> bool :=
  fold (&&) true.

Definition app {α} : list α -> list α -> list α :=
  flip (fold (::)).
Notation "xs ++ ys" := (app xs ys).
Compute [1; 2; 3] ++ [4; 5; 6].

Definition length {α} : list α -> nat := fold (const (+1)) 0.
Compute length ([1; 2; 3] ++ [4; 5; 6]).

Definition reverse {α} : list α -> list α :=
  let snoc x xs := xs ++ [x] in
  fold snoc [].

Definition map {α β} (f : α -> β) : list α -> list β :=
  fold (λ x rec, f x :: rec) [].

Definition filter {α} (p : α -> bool) :=
  fold (λ x rec, if p x then x :: rec else rec) [].


(** Fold fusion *)

Lemma fold_fusion {α β γ} (f : α -> β -> β) (v : β)
                          (g : α -> γ -> γ) (w : γ)
                          (h : γ -> β) :
  h w = v ->
  (∀ x y, h (g x y) = f x (h y)) ->
  (h ∘ fold g w) =1 fold f v.
Proof.
move=> E1 E2.
by elim => //= x xs IH; rewrite E2 IH.
Qed.

(* manual approach *)
Lemma fold_fusion_step_by_step {α β γ}
        (f : α -> β -> β) (v : β) (g : α -> γ -> γ) (w : γ) (h : γ -> β) :
  h w = v ->
  (∀ x y, h (g x y) = f x (h y)) ->
  (h ∘ fold g w) =1 fold f v.
Proof.
move=> E1.
move=> E2.
Print "=1".
(* Unset Printing Notations. *)
rewrite /eqfun.
move=> xs.
elim: xs.
- rewrite /comp.
  rewrite /fold.
  (* move=> /= *)
  rewrite E1.
  reflexivity.
move=> x xs InductionHypothesis.
Fail rewrite InductionHypothesis.
move=> /=.
rewrite -InductionHypothesis.
move=> /=.
rewrite E2.
reflexivity.
Qed.

(* more automation *)
Lemma fold_fusion_auto {α β γ} (f : α -> β -> β) (v : β)
        (g : α -> γ -> γ) (w : γ) (h : γ -> β) :
  h w = v ->
  (∀ x y, h (g x y) = f x (h y)) ->
  (h ∘ fold g w) =1 fold f v.
Proof. by move=> *; elim => /=; congruence. Qed.

(* examples of fold_fusion usage *)
Lemma sum_fusion_by_induction :
  (+1) ∘ sum =1 fold (+) 1.
Proof. by elim => //= ?? <-. Qed.

Lemma sum_fusion_by_fold_fusion_lemma :
  (+1) ∘ sum =1 fold (+) 1.
Proof. by apply: fold_fusion. Qed.

Lemma map_fusion {α β γ} (g : α -> β) (f : β -> γ) :
  map f ∘ map g =1 map (f ∘ g).
Proof. by apply: fold_fusion. Qed.


(** Recursors vs Iterators *)

Equations dropWhile_rec {α} (p : α -> bool) (xs : list α) : list α :=
dropWhile_rec p [] := [];
dropWhile_rec p (cons x xs) := if p x then dropWhile_rec p xs else (cons x xs).

(* fold is basically an iterator *)
(* but to implement dropWhile via fold we need a recursor,
   because we need to access the tail of the list *)

(* serves as a spec *)
Equations foldRec {α β} (f : α -> list α -> β -> β) (v : β) (xs : list α) : β :=
foldRec f v []            := v ;
foldRec f v (cons h tail) := f h tail (foldRec f v tail).

Definition foldRec_aux' {α β} (f : α -> list α -> β -> β) (v : β) :
                               list α -> (list α * β) :=
  fold (λ x '(xs, rec), (x :: xs, f x xs rec))
       ([], v).

Definition foldRec' {α β} (f : α -> list α -> β -> β) (v : β) : list α -> β :=
  snd ∘ foldRec_aux' f v.

Lemma foldRec_aux'_spec {α β} (f : α -> list α -> β -> β) (v : β) xs :
  foldRec_aux' f v xs = (xs, foldRec f v xs).
Proof.
by rewrite /foldRec_aux'; elim: xs => //= ??; case: fold; move => ?? [->->].
Qed.

Lemma foldRec_eq_foldRec' {α β} (f : α -> list α -> β -> β) (v : β) :
  foldRec f v =1 foldRec' f v.
Proof. by move=>*; rewrite /foldRec' /= foldRec_aux'_spec. Qed.

Definition dropWhile {α} (p : α -> bool) : list α -> list α :=
  foldRec' (λ h tail rec, if p h then rec else h :: tail) [].

Lemma dropWhile_rec_eq_dropWhile {α} (p : α -> bool) :
  dropWhile_rec p =1 dropWhile p.
Proof.
elim => //= h tl ->.
by rewrite /dropWhile /foldRec' /= !foldRec_aux'_spec.
Qed.


(** fold and foldl *)

Equations foldl_rec {α β} (f : β -> α -> β) (v : β) (xs : list α) : β :=
foldl_rec f v [] := v;
foldl_rec f v (cons x xs) := foldl_rec f (f v x) xs.

Definition foldl_fold {α β} (f : β -> α -> β) (v : β) (xs : list α) : β :=
  fold (λ x rec, rec ∘ (flip f x)) id xs v.

Lemma foldl_fold_eq_foldl_rec {α β} (f : β -> α -> β) v :
  foldl_fold f v =1 foldl_rec f v.
Proof. by rewrite /foldl_fold; move=> xs; elim: xs v => //= x xs ->. Qed.

(* another approach using composition *)
Definition foldl_rev {α β} (f : β -> α -> β) (v : β) : list α -> β :=
  (fold (flip f) v) ∘ reverse.

(* helper *)
Lemma reverse_cons {α} (x : α) xs :
  reverse (x :: xs) = reverse xs ++ [x].
Proof. by []. Qed.

(* helper *)
Lemma fold_app {α β} (f : α -> β -> β) v xs ys :
  fold f v (xs ++ ys) = fold f (fold f v ys) xs.
Proof. by elim: xs => //= ?? ->. Qed.

Lemma foldl_rec_eq_foldl_rev {α β} (f : β -> α -> β) v :
  foldl_rec f v =1 foldl_rev f v.
Proof.
rewrite /foldl_rev; move=> xs; elim: xs v => //= x xs IH v.
by rewrite IH reverse_cons fold_app.
Qed.


(** Ackermann's function *)

Definition pmapd {A B} (f : A -> B) (p : (A * A)) : (B * B) :=
  let '(a1, a2) := p in (f a1, f a2).

(* we have to define the Ackermann function on pair of arguments
   because [by rec] expects one single argument *)
Equations ack_rec (xsys : list nat * list nat) : list nat :=
ack_rec xsys by rec xsys (MR (lexprod _ _ lt lt) (pmapd (@length nat))) :=
ack_rec (pair [] ys) := 1 :: ys;
ack_rec (pair (cons x xs) []) := ack_rec (xs, [1]);
ack_rec (pair (cons x xs) (cons y ys)) := ack_rec (xs, ack_rec (x :: xs, ys)).

(* will compute with https://github.com/mattam82/Coq-Equations/pull/90 *)
(* Example ack_rec_test1 : ack_rec ([1], [1;1]) = [1;1;1;1] := eq_refl. *)
(* Example ack_rec_test2 : ack_rec ([1;1], [1;1]) = [1;1;1;1;1;1;1] := eq_refl. *)

Definition ack : list nat -> list nat -> list nat :=
  fold (λ x g, fold (λ y, g) (g [1])) ((::) 1).

Example ack_test1 : ack [1] [1;1] = [1;1;1;1] := eq_refl.
Example ack_test2 : ack [1;1] [1;1] = [1;1;1;1;1;1;1] := eq_refl.
Example ack_test3 : length (ack [1;1;1] [1;1;1;1]) = 125 := eq_refl.


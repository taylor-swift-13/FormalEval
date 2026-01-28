Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

Inductive Any : Type :=
| AnyInt : Z -> Any
| AnyFloat : R -> Any
| AnyString : string -> Any
| AnyBool : bool -> Any
| AnyNone : Any.

Definition int := Z.

Inductive IsInt : Any -> int -> Prop :=
| IsInt_intro : forall z, IsInt (AnyInt z) z.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m H1 H2.
  inversion H1; inversion H2; subst.
  reflexivity.
Qed.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Example test_filter_integers_custom : 
  filter_integers_spec 
    [AnyString "apple"; AnyFloat (IZR 2); AnyNone; AnyBool false; AnyString "watermelon"; AnyInt 42%Z; AnyFloat (IZR 2)] 
    [42%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  { intros n H. inversion H. }
  apply fir_cons_nonint.
  { intros n H. inversion H. }
  apply fir_cons_nonint.
  { intros n H. inversion H. }
  apply fir_cons_nonint.
  { intros n H. inversion H. }
  apply fir_cons_nonint.
  { intros n H. inversion H. }
  apply fir_cons_int with (n := 42%Z).
  { apply IsInt_intro. }
  apply fir_cons_nonint.
  { intros n H. inversion H. }
  apply fir_nil.
Qed.
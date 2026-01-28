Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Inductive Any : Type :=
| AnyInt (z : Z)
| AnyStr (s : string)
| AnyList (l : list Any).

Definition int := Z.

Inductive IsInt : Any -> int -> Prop :=
| IsInt_intro : forall z, IsInt (AnyInt z) z.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m H1 H2.
  inversion H1; subst.
  inversion H2; subst.
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

Example test_filter_integers_complex : 
  filter_integers_spec 
    [AnyInt 1; AnyList [AnyInt 2; AnyStr "3"]; AnyStr "4"; AnyList [AnyStr "5"; AnyInt 6]; AnyInt 7; AnyList [AnyInt 2; AnyStr "3"]; AnyInt 1] 
    [1; 7; 1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1). constructor.
  apply fir_cons_nonint. intros n H; inversion H.
  apply fir_cons_nonint. intros n H; inversion H.
  apply fir_cons_nonint. intros n H; inversion H.
  apply fir_cons_int with (n := 7). constructor.
  apply fir_cons_nonint. intros n H; inversion H.
  apply fir_cons_int with (n := 1). constructor.
  apply fir_nil.
Qed.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Inductive Any :=
| AInt : Z -> Any
| AStr : string -> Any
| ARealString : string -> Any
| AList : list Any -> Any
| AMap : Any.

Definition int := Z.

Inductive IsInt : Any -> int -> Prop :=
| IsInt_AInt : forall z, IsInt (AInt z) z.

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

Example test_case_mixed:
  filter_integers_spec
    [AInt 1%Z; AStr "33"%string; AInt 4%Z; ARealString "5.6"%string; AList []; AMap; AInt 1%Z; AInt 4%Z; AInt 4%Z; AInt 4%Z; AInt 4%Z; AInt 4%Z]
    [1%Z; 4%Z; 1%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int. constructor.
  eapply fir_cons_nonint. intros n H. inversion H.
  eapply fir_cons_int. constructor.
  eapply fir_cons_nonint. intros n H. inversion H.
  eapply fir_cons_nonint. intros n H. inversion H.
  eapply fir_cons_nonint. intros n H. inversion H.
  eapply fir_cons_int. constructor.
  eapply fir_cons_int. constructor.
  eapply fir_cons_int. constructor.
  eapply fir_cons_int. constructor.
  eapply fir_cons_int. constructor.
  eapply fir_cons_int. constructor.
  constructor.
Qed.
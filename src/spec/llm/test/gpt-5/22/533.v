Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Inductive Any : Type :=
| AInt : Z -> Any
| AList : list Any -> Any
| AStr : string -> Any
| ADictEmpty : Any.

Definition int := Z.
Definition IsInt (v : Any) (n : int) : Prop := v = AInt n.
Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof. intros v n m H1 H2. unfold IsInt in *. congruence. Qed.

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

Example test_case_complex: filter_integers_spec
  [AInt 1%Z; AInt 1%Z; AList [AInt 2%Z; AInt 3%Z]; AInt 4%Z; AList [AInt 5%Z];
   AInt 0%Z; AList []; AInt 1%Z; AList [AInt 7%Z; AStr "8"%string]; ADictEmpty; AStr "9rHiG"%string; AStr "9"%string]
  [1%Z; 1%Z; 4%Z; 0%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int. reflexivity.
  eapply fir_cons_int. reflexivity.
  eapply fir_cons_nonint. intros n H. discriminate.
  eapply fir_cons_int. reflexivity.
  eapply fir_cons_nonint. intros n H. discriminate.
  eapply fir_cons_int. reflexivity.
  eapply fir_cons_nonint. intros n H. discriminate.
  eapply fir_cons_int. reflexivity.
  eapply fir_cons_nonint. intros n H. discriminate.
  eapply fir_cons_nonint. intros n H. discriminate.
  eapply fir_cons_nonint. intros n H. discriminate.
  eapply fir_cons_nonint. intros n H. discriminate.
  constructor.
Qed.
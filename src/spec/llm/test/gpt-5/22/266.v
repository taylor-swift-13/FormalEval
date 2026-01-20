Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

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

Parameter a1 a2 a3 a4 a5 a6 a7 : Any.
Parameter n1 : int.
Axiom H1 : IsInt a1 n1.
Axiom Hnon2 : forall n, ~ IsInt a2 n.
Axiom Hnon3 : forall n, ~ IsInt a3 n.
Axiom Hnon4 : forall n, ~ IsInt a4 n.
Axiom Hnon5 : forall n, ~ IsInt a5 n.
Axiom Hnon6 : forall n, ~ IsInt a6 n.
Axiom Hnon7 : forall n, ~ IsInt a7 n.

Example test_case_single_int: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7] [n1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H1|].
  eapply fir_cons_nonint; [exact Hnon2|].
  eapply fir_cons_nonint; [exact Hnon3|].
  eapply fir_cons_nonint; [exact Hnon4|].
  eapply fir_cons_nonint; [exact Hnon5|].
  eapply fir_cons_nonint; [exact Hnon6|].
  eapply fir_cons_nonint; [exact Hnon7|].
  constructor.
Qed.
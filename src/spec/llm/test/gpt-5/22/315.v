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

Example test_case_mixed:
  forall (v2 v4 v_foneour v_5p5 v6 v_seven v_8 v_9 : Any) (n2 n4 n6 : int),
    IsInt v2 n2 ->
    IsInt v4 n4 ->
    IsInt v6 n6 ->
    (forall n, ~ IsInt v_foneour n) ->
    (forall n, ~ IsInt v_5p5 n) ->
    (forall n, ~ IsInt v_seven n) ->
    (forall n, ~ IsInt v_8 n) ->
    (forall n, ~ IsInt v_9 n) ->
    filter_integers_spec
      [v2; v4; v_foneour; v_5p5; v6; v_seven; v_8; v_9]
      [n2; n4; n6].
Proof.
  intros v2 n2 v4 n4 v_foneour v_5p5 v6 n6 v_seven v_8 v_9 H2 H4 H6 Hnf Hn5 Hns Hn8 Hn9.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H2|].
  eapply fir_cons_int; [exact H4|].
  eapply fir_cons_nonint; [exact Hnf|].
  eapply fir_cons_nonint; [exact Hn5|].
  eapply fir_cons_int; [exact H6|].
  eapply fir_cons_nonint; [exact Hns|].
  eapply fir_cons_nonint; [exact Hn8|].
  eapply fir_cons_nonint; [exact Hn9|].
  constructor.
Qed.
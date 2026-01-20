Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameter v2 v3 v_four v_55 v5a v_seven v_8 v_90 v_90b v_four2 v5b : Any.
Axiom IsInt_v2_2 : IsInt v2 2%Z.
Axiom IsInt_v3_3 : IsInt v3 3%Z.
Axiom NonInt_v_four : forall n, ~ IsInt v_four n.
Axiom NonInt_v_55 : forall n, ~ IsInt v_55 n.
Axiom IsInt_v5a_5 : IsInt v5a 5%Z.
Axiom NonInt_v_seven : forall n, ~ IsInt v_seven n.
Axiom NonInt_v_8 : forall n, ~ IsInt v_8 n.
Axiom NonInt_v_90 : forall n, ~ IsInt v_90 n.
Axiom NonInt_v_90b : forall n, ~ IsInt v_90b n.
Axiom NonInt_v_four2 : forall n, ~ IsInt v_four2 n.
Axiom IsInt_v5b_5 : IsInt v5b 5%Z.

Example test_case_mixed:
  filter_integers_spec
    [v2; v3; v_four; v_55; v5a; v_seven; v_8; v_90; v_90b; v_four2; v5b]
    [2%Z; 3%Z; 5%Z; 5%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v2_2 |].
  eapply fir_cons_int; [apply IsInt_v3_3 |].
  eapply fir_cons_nonint; [apply NonInt_v_four |].
  eapply fir_cons_nonint; [apply NonInt_v_55 |].
  eapply fir_cons_int; [apply IsInt_v5a_5 |].
  eapply fir_cons_nonint; [apply NonInt_v_seven |].
  eapply fir_cons_nonint; [apply NonInt_v_8 |].
  eapply fir_cons_nonint; [apply NonInt_v_90 |].
  eapply fir_cons_nonint; [apply NonInt_v_90b |].
  eapply fir_cons_nonint; [apply NonInt_v_four2 |].
  eapply fir_cons_int; [apply IsInt_v5b_5 |].
  apply fir_nil.
Qed.
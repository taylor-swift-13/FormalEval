Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

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

Parameter v_false v_none1 v5 v_neg6 v0 v_a v_b v_dict1 v_dict2 v_list34 v_list56_7 v_dict3 v_none2 : Any.

Axiom NonInt_false : forall n, ~ IsInt v_false n.
Axiom NonInt_none1 : forall n, ~ IsInt v_none1 n.
Axiom NonInt_a : forall n, ~ IsInt v_a n.
Axiom NonInt_b : forall n, ~ IsInt v_b n.
Axiom NonInt_dict1 : forall n, ~ IsInt v_dict1 n.
Axiom NonInt_dict2 : forall n, ~ IsInt v_dict2 n.
Axiom NonInt_list34 : forall n, ~ IsInt v_list34 n.
Axiom NonInt_list56_7 : forall n, ~ IsInt v_list56_7 n.
Axiom NonInt_dict3 : forall n, ~ IsInt v_dict3 n.
Axiom NonInt_none2 : forall n, ~ IsInt v_none2 n.

Axiom IsInt_v5 : IsInt v5 5%Z.
Axiom IsInt_vneg6 : IsInt v_neg6 (-6)%Z.
Axiom IsInt_v0 : IsInt v0 0%Z.

Example test_case_complex: filter_integers_spec
  [v_false; v_none1; v5; v_neg6; v0; v_a; v_b; v_dict1; v_dict2; v_list34; v_list56_7; v_dict3; v_none2]
  [5%Z; (-6)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_false |].
  eapply fir_cons_nonint; [apply NonInt_none1 |].
  eapply fir_cons_int; [apply IsInt_v5 |].
  eapply fir_cons_int; [apply IsInt_vneg6 |].
  eapply fir_cons_int; [apply IsInt_v0 |].
  eapply fir_cons_nonint; [apply NonInt_a |].
  eapply fir_cons_nonint; [apply NonInt_b |].
  eapply fir_cons_nonint; [apply NonInt_dict1 |].
  eapply fir_cons_nonint; [apply NonInt_dict2 |].
  eapply fir_cons_nonint; [apply NonInt_list34 |].
  eapply fir_cons_nonint; [apply NonInt_list56_7 |].
  eapply fir_cons_nonint; [apply NonInt_dict3 |].
  eapply fir_cons_nonint; [apply NonInt_none2 |].
  constructor.
Qed.
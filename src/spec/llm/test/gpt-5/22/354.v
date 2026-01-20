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

Parameters v_str v_real v_list v_set v_int1 v_int4a v_int4b : Any.
Axiom H_nonint_str : forall n, ~ IsInt v_str n.
Axiom H_nonint_real : forall n, ~ IsInt v_real n.
Axiom H_nonint_list : forall n, ~ IsInt v_list n.
Axiom H_nonint_set : forall n, ~ IsInt v_set n.
Axiom H_int1 : IsInt v_int1 1%Z.
Axiom H_int4a : IsInt v_int4a 4%Z.
Axiom H_int4b : IsInt v_int4b 4%Z.

Example test_case_new: filter_integers_spec [v_str; v_real; v_list; v_set; v_int1; v_int4a; v_int4b] [1%Z; 4%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - apply H_nonint_str.
  - eapply fir_cons_nonint.
    + apply H_nonint_real.
    + eapply fir_cons_nonint.
      * apply H_nonint_list.
      * eapply fir_cons_nonint.
        -- apply H_nonint_set.
        -- eapply fir_cons_int.
           ++ apply H_int1.
           ++ eapply fir_cons_int.
              ** apply H_int4a.
              ** eapply fir_cons_int.
                 --- apply H_int4b.
                 --- apply fir_nil.
Qed.
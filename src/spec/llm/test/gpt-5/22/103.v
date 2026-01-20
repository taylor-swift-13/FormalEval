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

Parameter v1 v_str2 v_obj_three v_list123 v_list45 v_obj_six : Any.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom NotInt_v_str2 : forall n, ~ IsInt v_str2 n.
Axiom NotInt_v_obj_three : forall n, ~ IsInt v_obj_three n.
Axiom NotInt_v_list123 : forall n, ~ IsInt v_list123 n.
Axiom NotInt_v_list45 : forall n, ~ IsInt v_list45 n.
Axiom NotInt_v_obj_six : forall n, ~ IsInt v_obj_six n.

Example test_case_mixed: filter_integers_spec [v1; v_str2; v_obj_three; v_list123; v_list45; v_obj_six] [1%Z].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int v1 1%Z [v_str2; v_obj_three; v_list123; v_list45; v_obj_six] []).
  - exact IsInt_v1.
  - apply (fir_cons_nonint v_str2 [v_obj_three; v_list123; v_list45; v_obj_six] []).
    + exact NotInt_v_str2.
    + apply (fir_cons_nonint v_obj_three [v_list123; v_list45; v_obj_six] []).
      * exact NotInt_v_obj_three.
      * apply (fir_cons_nonint v_list123 [v_list45; v_obj_six] []).
        -- exact NotInt_v_list123.
        -- apply (fir_cons_nonint v_list45 [v_obj_six] []).
           ++ exact NotInt_v_list45.
           ++ apply (fir_cons_nonint v_obj_six [] []).
              ** exact NotInt_v_obj_six.
              ** constructor.
Qed.
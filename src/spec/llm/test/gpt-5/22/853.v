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

Parameters
  v0 vFalse1 vStr3 v4 vFloatList v61 vTrue vEmptyStr vDict vFalse2 : Any.

Axiom IsInt_v0 : IsInt v0 0%Z.
Axiom IsInt_v4 : IsInt v4 4%Z.
Axiom IsInt_v61 : IsInt v61 61%Z.

Axiom NotInt_vFalse1 : forall n:int, ~ IsInt vFalse1 n.
Axiom NotInt_vStr3 : forall n:int, ~ IsInt vStr3 n.
Axiom NotInt_vFloatList : forall n:int, ~ IsInt vFloatList n.
Axiom NotInt_vTrue : forall n:int, ~ IsInt vTrue n.
Axiom NotInt_vEmptyStr : forall n:int, ~ IsInt vEmptyStr n.
Axiom NotInt_vDict : forall n:int, ~ IsInt vDict n.
Axiom NotInt_vFalse2 : forall n:int, ~ IsInt vFalse2 n.

Example test_case:
  filter_integers_spec
    [v0; vFalse1; vStr3; v4; vFloatList; v61; vTrue; vEmptyStr; vDict; vFalse2]
    [0%Z; 4%Z; 61%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - apply IsInt_v0.
  - eapply fir_cons_nonint.
    + apply NotInt_vFalse1.
    + eapply fir_cons_nonint.
      * apply NotInt_vStr3.
      * eapply fir_cons_int.
        -- apply IsInt_v4.
        -- eapply fir_cons_nonint.
           ++ apply NotInt_vFloatList.
           ++ eapply fir_cons_int.
              ** apply IsInt_v61.
              ** eapply fir_cons_nonint.
                 --- apply NotInt_vTrue.
                 --- eapply fir_cons_nonint.
                     +++ apply NotInt_vEmptyStr.
                     +++ eapply fir_cons_nonint.
                         *** apply NotInt_vDict.
                         *** eapply fir_cons_nonint.
                             ---- apply NotInt_vFalse2.
                             ---- apply fir_nil.
Qed.
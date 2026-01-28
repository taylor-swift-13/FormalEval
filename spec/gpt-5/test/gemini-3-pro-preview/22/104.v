Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter inj_Z : Z -> Any.
Parameter inj_str : string -> Any.
Parameter inj_list : list Any -> Any.

Axiom IsInt_inj_Z : forall z, IsInt (inj_Z z) z.
Axiom Not_IsInt_inj_str : forall s n, ~ IsInt (inj_str s) n.
Axiom Not_IsInt_inj_list : forall l n, ~ IsInt (inj_list l) n.

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

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [inj_Z 1; inj_list [inj_Z 2; inj_str "3"]; inj_str "4"; inj_list [inj_str "5"; inj_Z 6]; inj_Z 7] 
    [1; 7].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1).
  - apply IsInt_inj_Z.
  - apply fir_cons_nonint.
    + apply Not_IsInt_inj_list.
    + apply fir_cons_nonint.
      * apply Not_IsInt_inj_str.
      * apply fir_cons_nonint.
        -- apply Not_IsInt_inj_list.
        -- apply fir_cons_int with (n := 7).
           ++ apply IsInt_inj_Z.
           ++ apply fir_nil.
Qed.
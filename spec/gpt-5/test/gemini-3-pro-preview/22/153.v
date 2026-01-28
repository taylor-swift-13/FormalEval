Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope Z_scope.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter inj_Z : Z -> Any.
Parameter inj_list : list Any -> Any.
Parameter inj_str : string -> Any.

Axiom IsInt_inj_Z : forall z, IsInt (inj_Z z) z.
Axiom Not_IsInt_inj_list : forall l n, ~ IsInt (inj_list l) n.
Axiom Not_IsInt_inj_str : forall s n, ~ IsInt (inj_str s) n.

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

Example test_filter_integers_complex : 
  filter_integers_spec 
    [inj_Z 0; 
     inj_list [inj_Z 2; inj_str "3"]; 
     inj_list [inj_Z 4]; 
     inj_list [inj_Z 5; inj_Z 8; inj_Z 6; inj_Z 6]; 
     inj_list [inj_Z 5; inj_Z 8; inj_Z 6; inj_Z 6]; 
     inj_list [inj_Z 7; inj_Z 8]; 
     inj_Z 9; 
     inj_Z 1] 
    [0; 9; 1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 0).
  - apply IsInt_inj_Z.
  - apply fir_cons_nonint.
    + apply Not_IsInt_inj_list.
    + apply fir_cons_nonint.
      * apply Not_IsInt_inj_list.
      * apply fir_cons_nonint.
        -- apply Not_IsInt_inj_list.
        -- apply fir_cons_nonint.
           ++ apply Not_IsInt_inj_list.
           ++ apply fir_cons_nonint.
              ** apply Not_IsInt_inj_list.
              ** apply fir_cons_int with (n := 9).
                 --- apply IsInt_inj_Z.
                 --- apply fir_cons_int with (n := 1).
                     +++ apply IsInt_inj_Z.
                     +++ apply fir_nil.
Qed.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition s_off_foivife : string :=
  String.String (Ascii.ascii_of_nat 111)
    (String.String (Ascii.ascii_of_nat 102)
      (String.String (Ascii.ascii_of_nat 102)
        (String.String (Ascii.ascii_of_nat 10)
          (String.String (Ascii.ascii_of_nat 102)
            (String.String (Ascii.ascii_of_nat 111)
              (String.String (Ascii.ascii_of_nat 105)
                (String.String (Ascii.ascii_of_nat 118)
                  (String.String (Ascii.ascii_of_nat 105)
                    (String.String (Ascii.ascii_of_nat 102)
                      (String.String (Ascii.ascii_of_nat 101)
                        String.EmptyString)))))))))).

Example strlen_spec_off_foivife: strlen_spec s_off_foivife 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_off_foivife_Z: Z.of_nat (String.length s_off_foivife) = 11%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.
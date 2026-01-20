
Definition flip_case_spec (string : string) (result : string) : Prop :=
result = map Char.swapcase string.

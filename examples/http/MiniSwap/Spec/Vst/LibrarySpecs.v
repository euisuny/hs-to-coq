Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit.

(********************************** Library ***********************************)

Definition memset_spec :=
  DECLARE _memset
  WITH ptr : val, v : Z, n : Z, sh : share
  PRE [ 1%positive OF tptr tvoid,
        2%positive OF tint,
        3%positive OF tuint
      ]
  PROP ( writable_share sh ; 0 <= n <= Int.max_unsigned ) 
    LOCAL ( temp 1%positive ptr ;
              temp 2%positive (Vint (Int.repr v)) ;
              temp 3%positive (Vint (Int.repr n))
          )
    SEP ( data_at_ sh (tarray tuchar n) ptr )
  POST [ tptr tvoid ]
    PROP ( )
    LOCAL ( temp ret_temp ptr )
    SEP ( data_at sh (tarray tuchar n) 
                  (list_repeat (Z.to_nat n) (Vint (Int.repr v))) ptr
        ).

Definition memcpy_spec :=
  DECLARE _memcpy
  WITH contents : list val,
       dst_ptr : val,
       src_ptr : val,
       n : Z,
       dst_sh : share,
       src_sh : share
  PRE [ 1%positive OF tptr tvoid,
        2%positive OF tptr tvoid,
        3%positive OF tuint
      ]
    PROP ( 0 <= n <= Int.max_unsigned ; writable_share dst_sh;
           readable_share src_sh ) 
    LOCAL ( temp 1%positive dst_ptr ;
            temp 2%positive src_ptr;
            temp 3%positive (Vint (Int.repr n))
          )
    SEP ( data_at_ dst_sh (tarray tuchar n) dst_ptr ;
          data_at src_sh (tarray tuchar n) contents src_ptr
        )
  POST [ tptr tvoid ]
    PROP ( )
    LOCAL ( temp ret_temp dst_ptr )
    SEP ( data_at dst_sh (tarray tuchar n) contents dst_ptr ; 
          data_at src_sh (tarray tuchar n) contents src_ptr
        ).

Ltac forward_memcpy dst_ptr src_ptr len :=
  unfold tarray;
  match goal with
  | [|- context[data_at ?rsh (Tarray tuchar ?n ?attr) ?contents src_ptr]] =>
    match goal with
    | [|- context[data_at ?dsh _ _ dst_ptr]] =>
      forward_call (contents, dst_ptr, src_ptr, n, dsh, rsh)
    | [|- context[data_at_ ?dsh _ dst_ptr]] =>
      forward_call (contents, dst_ptr, src_ptr, n, dsh, rsh)
    end
  end.
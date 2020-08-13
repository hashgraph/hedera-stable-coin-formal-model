requires "hcs.k"

module DELEGABLE-SPEC
imports HCS

/*
  Approve

  Pre-conditions
      * Owner != 0x
      * value >= 0
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(spender)

  Post-conditions
      * Allowances[caller][spender] = value  
 */
rule <k> approveAllowance(Spender:Int, Value:Int, { caller : Caller } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <allowances>
      ...
      <allowance>
         <allower> Caller </allower>
         <spenders> ... (Spender |-> _ => Spender |-> Value) ... </spenders>
       </allowance>
       ...
     </allowances>
     <kycpassed> ... (Caller |-> true)(Spender |-> true) ... </kycpassed>
     <frozen> ... (Caller |-> false)(Spender |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool Value >=Int 0

/*
  Allowance approval followed by another allowance approval should ignore the first call.

  Pre-conditions
      * Owner != 0x
      * value1 >= 0
      * value2 >= 0
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(spender)

  Post-conditions
      * Allowances[caller][spender] = value2
 */
rule <k> approveAllowance(Spender:Int, Value1:Int, { caller : Caller } )
         ~>
         approveAllowance(Spender:Int, Value2:Int, { caller : Caller } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <allowances>
      ...
      <allowance>
         <allower> Caller </allower>
         <spenders> ... (Spender |-> _ => Spender |-> Value2) ... </spenders>
       </allowance>
       ...
     </allowances>
     <kycpassed> ... (Caller |-> true)(Spender |-> true) ... </kycpassed>
     <frozen> ... (Caller |-> false)(Spender |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool Value1 >=Int 0
    andBool Value2 >=Int 0

/*
  Approval fails if one of the pre-conditions is not satisfied

  Pre-conditions
      * Owner == 0x || value < 0 || !CheckTransferAllowed(caller) || !checkTransferAllowed(spender)

  Post-conditions
      * throws
 */
rule <k> approveAllowance(Spender:Int, Value:Int, { caller : Caller } ) => throw ...</k>
     <allowances>
         ...
         <allowance>
           <allower> Caller </allower>
           <spenders> ... (Spender |-> _) ... </spenders>
         </allowance>
         ...
     </allowances>
     <kycpassed> ... (Caller |-> CallerKyc)(Spender |-> SpenderKyc) ... </kycpassed>
     <frozen> ... (Caller |-> CallerFrozen)(Spender |-> SpenderFrozen) ... </frozen>
     <tokenOwner> TokenOwner </tokenOwner>
  requires TokenOwner ==Int 0
    orBool Value <Int 0
    orBool (notBool CallerKyc)
    orBool (notBool SpenderKyc)
    orBool CallerFrozen
    orBool SpenderFrozen
 
endmodule

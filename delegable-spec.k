requires "hcs.k"

module DELEGABLE-SPEC
imports HCS

// increase allowance: caller and spender exist
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

requires "hcs.k"

module UNCLASSIFIED-SPEC
imports HCS

// correctness of `setKycPassed` - changing from false to true
rule <k>setKycPassed(Target:Int, {caller: Caller}) => . ...</k>
     <tokenOwner> Owner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <kycpassed> ... (Target |-> _ => Target |-> true) ... </kycpassed>
  requires Owner =/=Int 0
    andBool Caller =/=Int 0
    andBool (Caller ==Int AssetProtectionManager orBool Caller ==Int Owner)

// correctness of `setKycPassed` - throw case (wrong caller)
rule <k> setKycPassed(_:Int, {caller: Caller}) => throw ...</k>
     <tokenOwner> Owner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
  requires Owner =/=Int 0
    andBool Caller =/=Int 0
    andBool (Caller =/=Int AssetProtectionManager andBool Caller =/=Int Owner)

// correctness of `unsetKycPassed` - good case
rule <k> unsetKycPassed(Account:Int, {caller: Caller}) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
     <kycpassed> ... (Account |-> _ => Account |-> false) ... </kycpassed>
  requires TokenOwner =/=Int 0
    andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
    andBool Account =/=Int TokenOwner
    andBool Account =/=Int SupplyManager
    andBool Account =/=Int AssetProtectionManager

// correctness of `unsetKycPassed` - throw if wrong person unsets
rule <k> unsetKycPassed(Account:Int, {caller: Caller}) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
  requires TokenOwner ==Int 0
    orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
    orBool Account ==Int TokenOwner
    orBool Account ==Int SupplyManager
    orBool Account ==Int AssetProtectionManager

// correctness of `freeze` - update
rule <k> freeze(Account:Int, {caller: Caller}) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
     <frozen> ... (Account |-> _ => Account |-> true) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
    andBool Account =/=Int TokenOwner
    andBool Account =/=Int SupplyManager
    andBool Account =/=Int AssetProtectionManager

// correctness of `freeze` - bad caller
rule <k> freeze(Account:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
  requires TokenOwner ==Int 0
    orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
    orBool Account ==Int TokenOwner
    orBool Account ==Int SupplyManager
    orBool Account ==Int AssetProtectionManager

// correctness of `unfreeze` - update
rule <k> unfreeze(Account:Int, {caller: Caller}) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <frozen> ... (Account |-> true => Account |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

// correctness of `unfreeze` - bad caller
rule <k> unfreeze(_:Int, {caller: Caller}) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
  requires TokenOwner ==Int 0
    orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)

// correctness of `freeze`, `unfreeze`, and then `freeze` again
rule <k> freeze(Account:Int, {caller: Caller})
         ~>
         unfreeze(Account:Int, {caller: Caller})
         ~>
         freeze(Account:Int, {caller: Caller}) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
     <frozen> ... (Account |-> _ => Account |-> true) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
    andBool Account =/=Int TokenOwner
    andBool Account =/=Int SupplyManager
    andBool Account =/=Int AssetProtectionManager

// correctness of `wipe` - update
rule <k> freeze(Account:Int, {caller: Caller})
         ~>
         wipe(Account, {caller: Caller}) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
     <frozen> ... (Account |-> false => Account |-> true) ... </frozen>
     <balances> ... (Account |-> Bal => Account |-> 0) ... </balances>
     <totalSupply> Supply => Supply -Int Bal </totalSupply>
  requires TokenOwner =/=Int 0
    andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
    andBool Account =/=Int TokenOwner
    andBool Account =/=Int SupplyManager
    andBool Account =/=Int AssetProtectionManager

// correctness of `wipe` - bad caller or not frozen
rule <k> wipe(Account:Int, {caller: Caller}) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <frozen> ... (Account |-> IsFrozen) ... </frozen>
     <balances> ... (Account |-> _) ... </balances>
  requires TokenOwner ==Int 0
    orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
    orBool (notBool IsFrozen)

// correctness of `isPrivilegedRole` - true
rule <k> isPrivilegedRole(Account:Int) => true ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <supplyManager> SupplyManager </supplyManager>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
  requires (TokenOwner =/=Int 0 orBool AssetProtectionManager =/=Int 0 orBool SupplyManager =/=Int 0)
    andBool (Account ==Int TokenOwner orBool Account ==Int AssetProtectionManager
    orBool Account ==Int SupplyManager)

// correctness of `isPrivilegedRole` - false
rule <k> isPrivilegedRole(Account:Int) => false ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
  requires notBool(Account ==Int TokenOwner
    orBool Account ==Int AssetProtectionManager orBool Account ==Int SupplyManager)

// increase allowance
rule <k> increaseAllowance(Spender:Int, Value:Int, { caller : Caller } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <allowances>
      ...
      <allowance>
         <allower> Caller </allower>
         <spenders> ... (Spender |-> OldAllowance => Spender |-> OldAllowance +Int Value) ... </spenders>
       </allowance>
       ...
     </allowances>
     <kycpassed> ... (Caller |-> true)(Spender |-> true) ... </kycpassed>
     <frozen> ... (Caller |-> false)(Spender |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool Value >=Int 0
    andBool (OldAllowance +Int Value) <=Int MAXVALUE
    andBool OldAllowance >=Int 0

rule <k> increaseAllowance(Spender:Int, Value1:Int, { caller : Caller } )
         ~>
         increaseAllowance(Spender:Int, Value2:Int, { caller : Caller } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <allowances>
      ...
      <allowance>
         <allower> Caller </allower>
         <spenders> ... (Spender |-> OldAllowance => Spender |-> OldAllowance +Int Value1 +Int Value2) ... </spenders>
       </allowance>
       ...
     </allowances>
     <kycpassed> ... (Caller |-> true)(Spender |-> true) ... </kycpassed>
     <frozen> ... (Caller |-> false)(Spender |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool Value1 >=Int 0
    andBool Value2 >=Int 0
    andBool (OldAllowance +Int Value1 +Int Value2) <=Int MAXVALUE
    andBool OldAllowance >=Int 0

rule <k> increaseAllowance(Spender:Int, Value:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <allowances>
      ...
      <allowance>
         <allower> Caller </allower>
         <spenders> ... (Spender |-> OldAllowance) ... </spenders>
       </allowance>
       ...
     </allowances>
     <kycpassed> ... (Caller |-> CallerKyc)(Spender |-> SpenderKyc) ... </kycpassed>
     <frozen> ... (Caller |-> CallerFrozen)(Spender |-> SpenderFrozen) ... </frozen>
  requires TokenOwner ==Int 0
    orBool Value <Int 0
    orBool (OldAllowance +Int Value) >Int MAXVALUE
    orBool OldAllowance <Int 0
    orBool (notBool CallerKyc)
    orBool (notBool SpenderKyc)
    orBool CallerFrozen
    orBool SpenderFrozen

// decrease allowance: success
rule <k> decreaseAllowance(Spender:Int, Value:Int, { caller : Caller } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <allowances>
      ...
      <allowance>
         <allower> Caller </allower>
         <spenders> ... (Spender |-> OldAllowance => Spender |-> OldAllowance -Int Value) ... </spenders>
       </allowance>
       ...
     </allowances>
     <kycpassed> ... (Caller |-> true)(Spender |-> true) ... </kycpassed>
     <frozen> ... (Caller |-> false)(Spender |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool Value >=Int 0
    andBool (OldAllowance -Int Value) >=Int 0
    andBool OldAllowance >=Int 0

rule <k> decreaseAllowance(Spender:Int, Value1:Int, { caller : Caller } )
         ~>
         decreaseAllowance(Spender:Int, Value2:Int, { caller : Caller } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <allowances>
      ...
      <allowance>
         <allower> Caller </allower>
         <spenders> ... (Spender |-> OldAllowance => Spender |-> OldAllowance -Int Value1 -Int Value2) ... </spenders>
       </allowance>
       ...
     </allowances>
     <kycpassed> ... (Caller |-> true)(Spender |-> true) ... </kycpassed>
     <frozen> ... (Caller |-> false)(Spender |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool Value1 >=Int 0
    andBool Value2 >=Int 0
    andBool (OldAllowance -Int Value1 -Int Value2) >=Int 0
    andBool OldAllowance >=Int 0

// decrease allowance: exception
rule <k> decreaseAllowance(Spender:Int, Value:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <allowances>
      ...
      <allowance>
         <allower> Caller </allower>
         <spenders> ... (Spender |-> OldAllowance) ... </spenders>
       </allowance>
       ...
     </allowances>
     <kycpassed> ... (Caller |-> CallerKyc)(Spender |-> SpenderKyc) ... </kycpassed>
     <frozen> ... (Caller |-> CallerFrozen)(Spender |-> SpenderFrozen) ... </frozen>
  requires TokenOwner ==Int 0
    orBool Value <Int 0
    orBool (OldAllowance -Int Value) <Int 0
    orBool OldAllowance <Int 0
    orBool (notBool CallerKyc)
    orBool (notBool SpenderKyc)
    orBool CallerFrozen
    orBool SpenderFrozen

// increase and then decrease allowance
rule <k> increaseAllowance(Spender:Int, Value1:Int, { caller : Caller } )
         ~>
         decreaseAllowance(Spender:Int, Value2:Int, { caller : Caller } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <allowances>
      ...
      <allowance>
         <allower> Caller </allower>
         <spenders> ... (Spender |-> OldAllowance => Spender |-> OldAllowance +Int Value1 -Int Value2) ... </spenders>
       </allowance>
       ...
     </allowances>
     <kycpassed> ... (Caller |-> true)(Spender |-> true) ... </kycpassed>
     <frozen> ... (Caller |-> false)(Spender |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool Value1 >=Int 0
    andBool Value2 >=Int 0
    andBool (OldAllowance +Int Value1) <=Int MAXVALUE
    andBool (OldAllowance +Int Value1 -Int Value2) >=Int 0
    andBool OldAllowance >=Int 0

// decrease and then increase allowance
rule <k> decreaseAllowance(Spender:Int, Value1:Int, { caller : Caller } )
         ~>
         increaseAllowance(Spender:Int, Value2:Int, { caller : Caller } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <allowances>
      ...
      <allowance>
         <allower> Caller </allower>
         <spenders> ... (Spender |-> OldAllowance => Spender |-> OldAllowance -Int Value1 +Int Value2) ... </spenders>
       </allowance>
       ...
     </allowances>
     <kycpassed> ... (Caller |-> true)(Spender |-> true) ... </kycpassed>
     <frozen> ... (Caller |-> false)(Spender |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool Value1 >=Int 0
    andBool Value2 >=Int 0
    andBool (OldAllowance -Int Value1) >=Int 0
    andBool (OldAllowance -Int Value1 +Int Value2) <=Int MAXVALUE
    andBool OldAllowance >=Int 0

endmodule

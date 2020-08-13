requires "hcs.k"

module UNCLASSIFIED-SPEC
imports HCS

/*
  Set KYC passed
  
  Pre-conditions
      * Owner != 0x
      * caller = AssetProtectionManager || caller = Owner

  Post-conditions
      * KycPassed[addr]
 */
rule <k>setKycPassed(Target:Int, {caller: Caller}) => . ...</k>
     <tokenOwner> Owner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <kycpassed> ... (Target |-> _ => Target |-> true) ... </kycpassed>
  requires Owner =/=Int 0
    andBool Caller =/=Int 0
    andBool (Caller ==Int AssetProtectionManager orBool Caller ==Int Owner)

// throws if pre-conditions are not satisfied
rule <k> setKycPassed(_:Int, {caller: Caller}) => throw ...</k>
     <tokenOwner> Owner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
  requires Owner =/=Int 0
    andBool Caller =/=Int 0
    andBool (Caller =/=Int AssetProtectionManager andBool Caller =/=Int Owner)

/*
  Unset passed KYC
  
  Pre-conditions
      * Owner != 0x
      * caller = AssetProtectionManager || caller = Owner
      * !isPrivilegedRole(addr)

  Post-conditions
      * !KycPassed[addr]
 */
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

// throws if pre-conditions are not satisfied
rule <k> unsetKycPassed(Account:Int, {caller: Caller}) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
  requires TokenOwner ==Int 0
    orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
    orBool Account ==Int TokenOwner
    orBool Account ==Int SupplyManager
    orBool Account ==Int AssetProtectionManager

/*
  Freeze
  
  Pre-conditions
      * Owner != 0x
      * caller = AssetProtectionManager || caller = Owner
      * !isPrivilegedRole(addr)

  Post-conditions
      * Frozen[addr] // upon completion, Frozen[addr] must be true
 */
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

// throws if pre-conditions are not satisfied
rule <k> freeze(Account:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
  requires TokenOwner ==Int 0
    orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
    orBool Account ==Int TokenOwner
    orBool Account ==Int SupplyManager
    orBool Account ==Int AssetProtectionManager

/*
  Unfreeze
  
  Pre-conditions
      * Owner != 0x
      * caller = AssetProtectionManager || caller = Owner

  Post-conditions
      * !Frozen[addr] // upon completion, Frozen[addr] must be false
 */
rule <k> unfreeze(Account:Int, {caller: Caller}) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <frozen> ... (Account |-> true => Account |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

// throws if pre-conditions are not satisfied
rule <k> unfreeze(_:Int, {caller: Caller}) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
  requires TokenOwner ==Int 0
    orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)

/*
  Freeze followed by unfreeze followed by freeze should leave the account frozen.
  
  Pre-conditions
      * Owner != 0x
      * caller = AssetProtectionManager || caller = Owner
      * !isPrivilegedRole(addr)

  Post-conditions
      * Frozen[addr] // upon completion, Frozen[addr] must be true
 */
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

/*
  Wipe can only be called for a frozen account.
  
  Pre-conditions
      * Owner != 0x
      * caller = AssetProtectionManager || caller = Owner
      * !isPrivilegedRole(addr)

  Post-conditions
      * Frozen[addr] // upon completion, Frozen[addr] must be true
      * TotalSupply’ = TotalSupply - Balances[addr] // total supply decreased
      * Balances[addr]’ = 0 // balance “updated” to 0  
 */
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

// throws if pre-conditions are not satisfied
rule <k> wipe(Account:Int, {caller: Caller}) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <frozen> ... (Account |-> IsFrozen) ... </frozen>
     <balances> ... (Account |-> _) ... </balances>
  requires TokenOwner ==Int 0
    orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
    orBool (notBool IsFrozen)

/*
  Is privileged role
  
  Pre-conditions
      * Owner != 0x
      * addr = Owner || addr = AssetProtectionManager || addr = SupplyManager

  Post-conditions
      * result = true
 */
rule <k> isPrivilegedRole(Account:Int) => true ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <supplyManager> SupplyManager </supplyManager>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
  requires (TokenOwner =/=Int 0 orBool AssetProtectionManager =/=Int 0 orBool SupplyManager =/=Int 0)
    andBool (Account ==Int TokenOwner orBool Account ==Int AssetProtectionManager
    orBool Account ==Int SupplyManager)

/*
  Is privileged role
  
  Pre-conditions
      * Owner != 0x
      * addr = !(Owner || addr = AssetProtectionManager || addr = SupplyManager)

  Post-conditions
      * result = false
 */
rule <k> isPrivilegedRole(Account:Int) => false ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
  requires notBool(Account ==Int TokenOwner
    orBool Account ==Int AssetProtectionManager orBool Account ==Int SupplyManager)

/*
  Increase allowance
  
  Pre-conditions
      * Owner != 0x
      * value >= 0
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(spender)
      * Allowances[caller][spender] + value <= MAX_INT

  Post-conditions
      * Allowances[caller][spender]’ = Allowances[caller][spender] + value
 */
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

/*
  Increase the allowance twice should result in a sum of the increases
  
  Pre-conditions
      * Owner != 0x
      * value1 >= 0
      * value2 >= 0
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(spender)
      * Allowances[caller][spender] + value1 + value2 <= MAX_INT

  Post-conditions
      * Allowances[caller][spender]’ = Allowances[caller][spender] + value1 + value2
 */
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

// throws if pre-conditions are not satisfied
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

/*
  Decrease allowance
  
  Pre-conditions
      * Owner != 0x
      * value >= 0
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(spender)
      * Allowances[caller][spender] >= value

  Post-conditions
      * Allowances[caller][spender]’ = Allowances[caller][spender] - value
 */
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

/*
  Increase the allowance twice should result in a sum of the decreases
  
  Pre-conditions
      * Owner != 0x
      * value1 >= 0
      * value2 >= 0
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(spender)
      * Allowances[caller][spender] - value1 - value2 >= 0

  Post-conditions
      * Allowances[caller][spender]’ = Allowances[caller][spender] - value1 - value2
 */
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

/*
  Increase of the allowance followed by a decrease should result in an increase by the difference
  
  Pre-conditions
      * Owner != 0x
      * value1 >= 0
      * value2 >= 0
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(spender)
      * Allowances[caller][spender] + value1 <= MAX_INT
      * Allowances[caller][spender] + value1 - value2 >= 0

  Post-conditions
      * Allowances[caller][spender]’ = Allowances[caller][spender] + value1 - value2
 */
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

/*
  Decrease of the allowance followed by an increase shoudl result in a decrease by the difference
  
  Pre-conditions
      * Owner != 0x
      * value1 >= 0
      * value2 >= 0
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(spender)
      * Allowances[caller][spender] - value1 >= 0
      * Allowances[caller][spender] - value1 + value2 <= MAX_INT

  Post-conditions
      * Allowances[caller][spender]’ = Allowances[caller][spender] - value1 + value2
 */
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

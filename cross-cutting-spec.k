requires "hcs.k"

module CROSS-CUTTING-SPEC
imports HCS

/*
  Mint followed by a burn will result in no changes to the totalSupply (disallowing overflow)
  and balance of supply manager

  Pre-conditions
      * Owner != 0x // constructor has been called
      * caller = SupplyManager || caller = Owner
      * value >= 0
      * TotalSupply + value <= MAX_INT // prevents overflow
      * TotalSupply >= Balances[SupplyManager]
      * Balances[SupplyManager] >= 0

  Post-conditions
      * TotalSupply’ = TotalSupply // no change in the total supply
      * Balances[SupplyManager]’ = Balances[SupplyManager] // no change in the balance

  Note that according to the spec, the funds go to SupplyManager even if the caller is Owner
 */
rule <k> mint(Value, {caller: Caller})
         ~>
         burn(Value, {caller: Caller}) => . ...</k>
     <balances> ... (SupplyManager |-> Balance) ... </balances>
     <tokenOwner> Owner </tokenOwner>
     <supplyManager> SupplyManager </supplyManager>
     <totalSupply> Supply </totalSupply>
  requires Owner =/=Int 0
    andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
    andBool Value >=Int 0
    andBool Supply >=Int Balance
    andBool Balance >=Int 0
    andBool Supply +Int Value <=Int MAXVALUE
 
/*
  Burn followed by a mint will result in no changes to the totalSupply (disallowing underflow)
  and balance of supply manager

  Pre-conditions
      * Owner != 0x // constructor has been called
      * caller = SupplyManager || caller = Owner
      * value >= 0
      * TotalSupply + value <= MAX_INT // prevents overflow
      * TotalSupply >= Balances[SupplyManager]
      * Balances[SupplyManager] >= 0

  Post-conditions
      * TotalSupply’ = TotalSupply // no change in the total supply
      * Balances[SupplyManager]’ = Balances[SupplyManager] // no change in the balance

  Note that according to the spec, the funds go to SupplyManager even if the caller is Owner
 */
rule <k> burn(Value, {caller: Caller})
         ~>
         mint(Value, {caller: Caller}) => . ...</k>
     <balances> ... (SupplyManager |-> Balance) ... </balances>
     <tokenOwner> Owner </tokenOwner>
     <supplyManager> SupplyManager </supplyManager>
     <totalSupply> Supply </totalSupply>
  requires Owner =/=Int 0
    andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
    andBool Value >=Int 0
    andBool Balance >=Int Value
    andBool Supply >=Int Balance
    andBool Supply <=Int MAXVALUE

/*
  Wipe tokens of a stale supply manager after freezing their assets.
  
  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * NewSupplyManager != 0x
      * CheckTransferAllowed(NewSupplyManager)
      * OldSupplyManager != Caller
      * OldSupplyManager != NewSupplyManager
      * OldSupplyManager != AssetProtectionManager

  Post-conditions
      * SupplyManager = NewSupplyManager
      * Frozen[OldSupplyManager]
      * TotalSupply’ = TotalSupply - Balances[OldSupplyManager]
      * Balances[OldSupplyManager]’ = 0
 */
rule <k> changeSupplyManager(SupplyManager, { caller : Caller } )
         ~>
         freeze(OldSupplyManager, {caller: Caller})
         ~>
         wipe(OldSupplyManager, {caller: Caller}) => . ...</k>
     <tokenOwner> Caller </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> OldSupplyManager => SupplyManager </supplyManager>
     <balances> ... (OldSupplyManager |-> Bal => OldSupplyManager |-> 0) ... </balances>
     <kycpassed> ... (SupplyManager |-> true) ... </kycpassed>
     <frozen> ... (SupplyManager |-> false)(OldSupplyManager |-> false => OldSupplyManager |-> true) ... </frozen>
     <totalSupply> Supply => Supply -Int Bal </totalSupply>
  requires Caller =/=Int 0
    andBool SupplyManager =/=Int 0
    andBool OldSupplyManager =/=Int Caller
    andBool OldSupplyManager =/=Int SupplyManager
    andBool OldSupplyManager =/=Int AssetProtectionManager

/*
  Approval of an allowance and then subsequent increase should result in an approval of the sum of the allowances.

  Pre-conditions
      * Owner != 0x
      * value1 >= 0
      * value2 >= 0
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(spender)
      * Allowances[caller][spender] + value1 + value2 <= MAX_INT

  Post-conditions
      * Allowances[caller][spender] = value1 + value2
 */
rule <k> approveAllowance(Spender:Int, Value1:Int, { caller : Caller } )
         ~>
         increaseAllowance(Spender, Value2:Int, { caller : Caller } ) => . ...</k>
       <allowances> 
         ...
         <allowance>
           <allower> Caller </allower>
           <spenders> ... (Spender |-> _ => Spender |-> Value1 +Int Value2) ... </spenders>
         </allowance>
         ...
       </allowances>
       <kycpassed> ... (Caller |-> true)(Spender |-> true) ... </kycpassed>
       <frozen> ... (Caller |-> false)(Spender |-> false) ... </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0
      andBool Value1 >=Int 0
      andBool Value2 >=Int 0
      andBool (Value1 +Int Value2) <=Int MAXVALUE

/*
  Approval of an allowance and then subsequent decrease should result in an approval of the difference of the allowances.

  Pre-conditions
      * Owner != 0x
      * value1 >= 0
      * value2 >= 0
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(spender)
      * value1 - value2 >= 0

  Post-conditions
      * Allowances[caller][spender] = value1 - value2
 */
rule <k> approveAllowance(Spender:Int, Value1:Int, { caller : Caller } )
         ~>
         decreaseAllowance(Spender, Value2:Int, { caller : Caller } ) => . ...</k>
       <allowances> 
         ...
         <allowance>
           <allower> Caller </allower>
           <spenders> ... (Spender |-> _ => Spender |-> Value1 -Int Value2) ... </spenders>
         </allowance>
         ...
       </allowances>
       <kycpassed> ... (Caller |-> true)(Spender |-> true) ... </kycpassed>
       <frozen> ... (Caller |-> false)(Spender |-> false) ... </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0
      andBool Value1 >=Int 0
      andBool Value2 >=Int 0
      andBool (Value1 -Int Value2) >=Int 0


/*
  Disallow transfers when an account is frozen.
  
  Pre-conditions
      * Owner != 0x
      * caller = AssetProtectionManager || caller = Owner
      * !isPrivilegedRole(From)
      * value >= 0
      * Balances[From] >= value
      * CheckTransferAllowed(From)
      * CheckTransferAllowed(To)

  Post-conditions
      * Frozen[From]
      * Balances[From]’ = Balances[From]
      * Balances[To]' = Balances[To]
 */
rule <k> freeze(From:Int, { caller : Caller } ) 
         ~>
         transfer(To:Int, Value:Int, { caller : From } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <supplyManager> SupplyManager </supplyManager>
       <frozen> ... (To |-> false)(From |-> _ => From |-> true) ... </frozen>
       <balances> ... (From |-> Balance)(To |-> _) ... </balances>
       <kycpassed> ... (To |-> true)(From |-> true) ... </kycpassed>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
      andBool From =/=Int TokenOwner
      andBool From =/=Int SupplyManager
      andBool From =/=Int AssetProtectionManager
      andBool To =/=Int From
      andBool Value >=Int 0
      andBool Balance >=Int Value

/*
  Allow transfers when an account is unfrozen.
  
  Pre-conditions
      * Owner != 0x
      * caller = AssetProtectionManager || caller = Owner
      * !isPrivilegedRole(From)
      * value >= 0
      * Balances[From] >= value
      * CheckTransferAllowed(From)
      * CheckTransferAllowed(To)

  Post-conditions
      * !Frozen[From]
      * Balances[From]’ = Balances[From] - value
      * Balances[To]' = Balances[To] + value
 */
rule <k> unfreeze(From:Int, {caller: Caller})
         ~>
         transfer(To:Int, Value:Int, { caller : From } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <kycpassed> ... (To |-> true) (From |-> true) ... </kycpassed>
     <frozen> ... (To |-> false) (From |-> _ => From |-> false) ... </frozen>
     <balances> ... (From |-> BalanceFrom => From |-> BalanceFrom -Int Value)
                    (To |-> BalanceTo => To |-> BalanceTo +Int Value) ... </balances>
  requires TokenOwner =/=Int 0
    andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
    andBool To =/=Int From
    andBool Value >=Int 0
    andBool BalanceFrom >=Int Value

endmodule
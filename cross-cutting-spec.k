requires "hcs.k"

module CROSS-CUTTING-SPEC
imports HCS

// A mint followed by a burn will result in no changes to the totalSupply (disallowing overflow)
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
 
// A burn followed by a mint will result in no changes to the totalSupply (disallowing underflow)
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

// wipe tokens of a stale supply manager
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

// approve and then increase allowance
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

// approve and then decrease allowance
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

// disallow transfers when an account is frozen
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

// allow transfers when an account is unfrozen
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
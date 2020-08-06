module HCS-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Value   ::= Int  // this can be changed
  syntax Address ::= Int  // this can be changed
  syntax AExp ::= Value | Address
                | "totalSupply" "(" ")"                                                                                 [strict]
                | "owner" "(" ")"                                                                                       [strict]
                | "supplyManager" "(" ")"                                                                               [strict]
                | "assetProtectionManager" "(" ")"                                                                      [strict]
                | "proposedOwner" "(" ")"                                                                               [strict]
                | "balanceOf" "(" AExp ")"                                                                              [strict]
                | "allowance" "(" AExp "," AExp ")"                                                                     [strict]
  syntax VExp ::= "constructor" "(" AExp "," AExp "," AExp "," AExp "," AExp "," AExp "," "{" "caller" ":" AExp "}" ")" [strict]
                | "approveAllowance" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                                [strict]
                | "increaseAllowance" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                               [strict]
                | "decreaseAllowance" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                               [strict]
                | "transfer" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                                        [strict]
                | "transferFrom" "(" AExp "," AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                           [strict]
                | "mint" "(" AExp "," "{" "caller" ":" AExp "}" ")"                                                     [strict]
                | "burn" "(" AExp "," "{" "caller" ":" AExp "}" ")"                                                     [strict]
                | "proposeOwner" "(" AExp "," "{" "caller" ":" AExp "}" ")"                                             [strict]
                | "claimOwnership" "(""{" "caller" ":" AExp "}" ")"                                                     [strict]
                | "changeSupplyManager" "(" AExp "," "{" "caller" ":" AExp "}" ")"                                      [strict]
                | "changeAssetProtectionManager" "(" AExp "," "{" "caller" ":" AExp "}" ")"                             [strict]
                | "setKycPassed" "(" AExp "," "{" "caller" ":" AExp "}" ")"                                             [strict]
                | "unsetKycPassed" "(" AExp "," "{" "caller" ":" AExp "}" ")"                                           [strict]
                | "freeze" "(" AExp "," "{" "caller" ":" AExp "}" ")"                                                   [strict]
                | "unfreeze" "(" AExp "," "{" "caller" ":" AExp "}" ")"                                                 [strict]
                | "wipe" "(" AExp "," "{" "caller" ":" AExp "}" ")"                                                     [strict]
                | "throw"
  syntax BExp ::= Bool
                | "isFrozen" "(" AExp ")"                                                                               [strict]
                | "isKycPassed" "(" AExp ")"                                                                            [strict]
                | "checkTransferAllowed" "(" AExp ")"                                                                   [strict]
                | "isPrivilegedRole" "(" AExp ")"                                                                       [strict]
endmodule

module HCS
  imports HCS-SYNTAX
  imports DOMAINS

  configuration <HCS unused="true">
                  <k> $PGM:K </k>
                  <balances>
                    .Map
                  </balances>
                  <frozen>
                    .Map
                  </frozen>
                  <kycpassed>
                    .Map
                  </kycpassed>
                  <allowances>
                    <allowance multiplicity="*" type="Map"> // Allower |-> Spenders
                      <allower> 0 </allower>
                      <spenders type="Map"> .Map </spenders> // Spender |-> Amount
                    </allowance>
                  </allowances>
                  <tokenName> 0 </tokenName>
                  <tokenSymbol> 0 </tokenSymbol>
                  <tokenDecimal> 0 </tokenDecimal>
                  <totalSupply> 0 </totalSupply>
                  <tokenOwner> 0 </tokenOwner>
                  <supplyManager> 0 </supplyManager>
                  <assetProtectionManager> 0 </assetProtectionManager>
                  <proposedOwner> 0 </proposedOwner>
                </HCS>

  syntax KResult ::= Int | Bool | String

  syntax Int ::= "MAXVALUE"  [function]
  rule MAXVALUE => 2 ^Int 256 -Int 1

// base

  rule <k> constructor(TokenNameArg, TokenSymbolArg, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } ) => . ...</k>
      <balances> Balances:Map => Balances [SupplyManagerArg <- TotalSupplyArg][Caller <- 0][AssetProtectionManagerArg <- 0] </balances>
      <kycpassed> KycPassed:Map => KycPassed[Caller <- true][SupplyManagerArg <- true][AssetProtectionManagerArg <- true] </kycpassed>
      <frozen> Frozen:Map => Frozen[Caller <- false][SupplyManagerArg <- false][AssetProtectionManagerArg <- false] </frozen>
      <allowances> 
         (.Bag =>
            <allowance>
              <allower> Caller </allower>
              <spenders> (0 |-> 0) </spenders>
            </allowance>
            <allowance>
              <allower> SupplyManagerArg </allower>
              <spenders> (0 |-> 0) </spenders>
            </allowance>
            <allowance>
              <allower> AssetProtectionManagerArg </allower>
              <spenders> (0 |-> 0) </spenders>
            </allowance>
         )
      </allowances>
      <tokenName> _ => TokenNameArg </tokenName>
      <tokenSymbol> _ => TokenSymbolArg </tokenSymbol>
      <tokenDecimal> _ => TokenDecimalArg </tokenDecimal>
      <totalSupply> _ => TotalSupplyArg </totalSupply>
      <tokenOwner> 0 => Caller </tokenOwner>
      <supplyManager> _ => SupplyManagerArg </supplyManager>
      <assetProtectionManager> _ => AssetProtectionManagerArg </assetProtectionManager>
      <proposedOwner> 0 </proposedOwner>
    requires TokenDecimalArg >=Int 0
      andBool TotalSupplyArg >=Int 0
      andBool Caller =/=Int 0
      andBool SupplyManagerArg =/=Int 0
      andBool AssetProtectionManagerArg =/=Int 0

  // constructor throws if it's called more than once or arguments are incorrect
  rule <k> constructor(_, _, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } ) => throw ...</k>
      <tokenOwner> TokenOwner </tokenOwner>
    requires notBool (TokenOwner ==Int 0
      andBool TokenDecimalArg >=Int 0
      andBool TotalSupplyArg >=Int 0
      andBool Caller =/=Int 0
      andBool SupplyManagerArg =/=Int 0
      andBool AssetProtectionManagerArg =/=Int 0)

// getters

  rule <k> totalSupply() => Total ...</k>
       <totalSupply> Total </totalSupply>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  rule <k> totalSupply() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  rule <k> balanceOf(Id) => (Balances[Id] orDefault 0) ...</k>
       <balances> Balances:Map </balances>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  rule <k> balanceOf(_) => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  rule <k> owner() => TokenOwner ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  rule <k> owner() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  rule <k> supplyManager() => SupplyManager ...</k>
       <supplyManager> SupplyManager </supplyManager>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  rule <k> supplyManager() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  rule <k> assetProtectionManager() => AssetProtectionManager ...</k>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  rule <k> assetProtectionManager() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  rule <k> proposedOwner() => ProposedOwner ...</k>
       <proposedOwner> ProposedOwner </proposedOwner>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  rule <k> proposedOwner() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  rule <k> isFrozen(Id) => (Frozen[Id] orDefault false) ...</k>
       <frozen> Frozen:Map </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  rule <k> isFrozen(_) => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  rule <k> isKycPassed(Id) => (KycPassed[Id] orDefault false) ...</k>
       <kycpassed> KycPassed:Map </kycpassed>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  rule <k> isKycPassed(_) => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  rule <k> allowance(Allower, Spender) => Value ... </k>
       <allowance>
         <allower> Allower </allower>
         <spenders> ... (Spender |-> Value) ... </spenders>
       </allowance>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0
  
  rule <k> allowance(_, _) => throw ... </k>
       <tokenOwner> 0 </tokenOwner>

// mintable

  // note that according to the spec, the funds go to SupplyManager even if the caller is Owner
  rule <k> mint(Value, { caller : Caller } ) => . ...</k>
       <balances> ... (SupplyManager |-> Balance => SupplyManager |-> Balance +Int Value) ... </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply => Supply +Int Value </totalSupply>
    requires Owner =/=Int 0
      andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
      andBool Value >=Int 0
      andBool Supply +Int Value <=Int MAXVALUE
      andBool Balance <=Int Supply

  rule <k> mint(Value, { caller : Caller } ) => throw ...</k>
       <balances> ... (SupplyManager |-> Balance) ... </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply </totalSupply>
    requires Owner ==Int 0
      orBool (Caller =/=Int SupplyManager andBool Caller =/=Int Owner)
      orBool Value <Int 0
      orBool Supply +Int Value >Int MAXVALUE
      orBool Balance >Int Supply

// burnable
  rule <k> burn(Value, { caller: Caller } ) => . ...</k>
       <balances> ... (SupplyManager |-> Balance => SupplyManager |-> Balance -Int Value) ... </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply => Supply -Int Value </totalSupply>
    requires Owner =/=Int 0
      andBool Balance >=Int Value
      andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
      andBool Value >=Int 0
      andBool Balance <=Int Supply

  rule <k> burn(Value, {caller: Caller}) => throw ...</k>
       <balances> ... (SupplyManager |-> Balance) ... </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply </totalSupply>
    requires Owner ==Int 0
      orBool Balance <Int Value
      orBool (Caller =/=Int SupplyManager andBool Caller =/=Int Owner)
      orBool Value <Int 0
      orBool Balance >Int Supply

// compliant

  // allowed if passed kyc and frozen is set to false
  rule <k> checkTransferAllowed(Account) => true ...</k>
      <kycpassed> ... (Account |-> true) ... </kycpassed>
      <frozen> ... (Account |-> false) ... </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // disallowed if passed kyc is unset or account is frozen
  rule <k> checkTransferAllowed(Account) => false ...</k>
      <kycpassed> ... (Account |-> KycPassed) ... </kycpassed>
      <frozen> ... (Account |-> Frozen) ... </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool (notBool KycPassed)
      orBool Frozen

// delegable

  // approve case: success
  rule <k> approveAllowance(Spender, Value, { caller : Caller } ) => . ...</k>
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
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0
      andBool Value >=Int 0

  // approve case: failure
  rule <k> approveAllowance(Spender, Value, { caller : Caller } ) => throw ...</k>
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

// transferable
 
  // transfer case: To =/= From, success 
  rule <k> transfer(To, Value, { caller : From } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <balances> ... (From |-> BalanceFrom => From |-> BalanceFrom -Int Value)
                      (To |-> BalanceTo => To |-> BalanceTo +Int Value) ... </balances>
       <kycpassed> ... (To |-> true) (From |-> true) ... </kycpassed>
       <frozen> ... (To |-> false) (From |-> false) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool To =/=Int From
      andBool Value >=Int 0
      andBool BalanceFrom >=Int Value

  // transfer case: To == From, success 
  rule <k> transfer(Account, Value, { caller : Account } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <balances> ... (Account |-> Balance) ... </balances>  
       <kycpassed> ... (Account |-> true) ... </kycpassed>
       <frozen> ... (Account |-> false) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool Value >=Int 0
      andBool Balance >=Int Value

  // transfer case: basic condition does not hold, fail
  rule <k> transfer(To, Value, { caller : From } ) => throw ...</k>
       <balances> ... (From |-> Balance)(To |-> _) ... </balances>  
       <kycpassed> ... (To |-> ToKyc) (From |-> FromKyc) ... </kycpassed>
       <frozen> ... (To |-> ToFrozen) (From |-> FromFrozen) ... </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool Value <Int 0
      orBool Balance <Int Value
      orBool (notBool ToKyc)
      orBool (notBool FromKyc)
      orBool ToFrozen
      orBool FromFrozen

  // transferFrom case: To =/= From, success
  rule <k> transferFrom(From, To, Value, {caller: Caller}) => . ... </k>
       <tokenOwner> TokenOwner </tokenOwner>
       <allowance>
         <allower> From </allower>
         <spenders> ... (Caller |-> Allowance => Caller |-> Allowance -Int Value) ... </spenders>
       </allowance>
       <balances> ... (From |-> BalanceFrom => From |-> BalanceFrom -Int Value)
                      (To |-> BalanceTo => To |-> BalanceTo +Int Value) ... </balances>
       <kycpassed> ... (To |-> true) (From |-> true) (Caller |-> true) ... </kycpassed>
       <frozen> ... (To |-> false) (From |-> false) (Caller |-> false) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool To =/=Int From
      andBool Value >=Int 0
      andBool BalanceFrom >=Int Value
      andBool Allowance >=Int Value

  // transferFrom case: To == From, success
  rule <k> transferFrom(From, From, Value, {caller: Caller}) => . ... </k>
       <tokenOwner> TokenOwner </tokenOwner>
       <allowance>
         <allower> From </allower>
         // still subtracting from allowance even though no funds actually moved
         <spenders> ... (Caller |-> Allowance => Caller |-> Allowance -Int Value) ... </spenders>
       </allowance>
       <balances> ... (From |-> Balance) ... </balances>  
       <kycpassed> ... (From |-> true) (Caller |-> true) ... </kycpassed>
       <frozen> ... (From |-> false) (Caller |-> false) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool Value >=Int 0
      andBool Balance >=Int Value
      andBool Allowance >=Int Value

  // transferFrom case: fail otherwise
  rule <k> transferFrom(From, From, Value, {caller: Caller}) => throw ... </k>
       <tokenOwner> TokenOwner </tokenOwner>
       <allowance>
         <allower> From </allower>
         <spenders> ... (Caller |-> Allowance) ... </spenders>
       </allowance>
       <balances> ... (From |-> Balance) ... </balances>  
       <kycpassed> ... (To |-> ToKyc) (From |-> FromKyc) (Caller |-> CallerKyc) ... </kycpassed>
       <frozen> ... (To |-> ToFrozen) (From |-> FromFrozen) (Caller |-> CallerFrozen) ... </frozen>
    requires TokenOwner ==Int 0
      orBool Value <Int 0
      orBool Balance <Int Value
      orBool Allowance <Int Value
      orBool (notBool ToKyc)
      orBool (notBool FromKyc)
      orBool (notBool CallerKyc)
      orBool ToFrozen
      orBool FromFrozen
      orBool CallerFrozen

// privileged roles

  rule <k> proposeOwner(ProposedOwner, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <proposedOwner> _ => ProposedOwner </proposedOwner>
       <kycpassed> ... (ProposedOwner |-> true) ... </kycpassed>
       <frozen> ... (ProposedOwner |-> false) ... </frozen>
    requires Caller =/=Int 0 andBool ProposedOwner =/=Int 0

  rule <k> proposeOwner(ProposedOwner, { caller : Caller } ) => throw ...</k>
       <kycpassed> ... (ProposedOwner |-> KycPassed) ... </kycpassed>
       <frozen> ... (ProposedOwner |-> Frozen) ... </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool TokenOwner =/=Int Caller
      orBool ProposedOwner ==Int 0
      orBool (notBool KycPassed)
      orBool Frozen

  rule <k> claimOwnership( { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner => Caller </tokenOwner>
       <proposedOwner> Caller => 0 </proposedOwner>
       <kycpassed> ... (Caller |-> true) ... </kycpassed>
       <frozen> ... (Caller |-> false) ... </frozen>
    requires Caller =/=Int 0 andBool TokenOwner =/=Int 0

  rule <k> claimOwnership( { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <proposedOwner> ProposedOwner </proposedOwner>
       <kycpassed> ... (Caller |-> KycPassed) ... </kycpassed>
       <frozen> ... (Caller |-> Frozen) ... </frozen>
    requires Caller ==Int 0
      orBool TokenOwner ==Int 0
      orBool Caller =/=Int ProposedOwner
      orBool (notBool KycPassed)
      orBool Frozen

  rule <k> changeSupplyManager(SupplyManager, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <supplyManager> _ => SupplyManager </supplyManager>
       <kycpassed> ... (SupplyManager |-> true) ... </kycpassed>
       <frozen> ... (SupplyManager |-> false) ... </frozen>
    requires Caller =/=Int 0 andBool SupplyManager =/=Int 0

  rule <k> changeSupplyManager(SupplyManager, { caller : Caller } ) => throw ...</k>
       <kycpassed> ... (SupplyManager |-> KycPassed) ... </kycpassed>
       <frozen> ... (SupplyManager |-> Frozen) ... </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool SupplyManager ==Int 0
      orBool Caller =/=Int TokenOwner 
      orBool (notBool KycPassed)
      orBool Frozen

  rule <k> changeAssetProtectionManager(AssetProtectionManager, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <assetProtectionManager> _ => AssetProtectionManager </assetProtectionManager>
       <kycpassed> ... (AssetProtectionManager |-> true) ... </kycpassed>
       <frozen> ... (AssetProtectionManager |-> false) ... </frozen>
    requires Caller =/=Int 0 andBool AssetProtectionManager =/=Int 0

  rule <k> changeAssetProtectionManager(AssetProtectionManager, { caller : Caller } ) => throw ...</k>
       <kycpassed> ... (AssetProtectionManager |-> KycPassed) ... </kycpassed>
       <frozen> ... (AssetProtectionManager |-> Frozen) ... </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool AssetProtectionManager ==Int 0
      orBool Caller =/=Int TokenOwner 
      orBool (notBool KycPassed)
      orBool Frozen

// unclassified

  rule <k> setKycPassed(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <kycpassed> ... (Account |-> _ => Account |-> true) ... </kycpassed>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
  
  rule <k> setKycPassed(_, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
  
  // unset kycpassed
  rule <k> unsetKycPassed(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <supplyManager> SupplyManager </supplyManager>
       <kycpassed> ... (Account |-> _ => Account |-> false) ... </kycpassed>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
      andBool Account =/=Int TokenOwner
      andBool Account =/=Int SupplyManager
      andBool Account =/=Int AssetProtectionManager

  rule <k> unsetKycPassed(Account, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <supplyManager> SupplyManager </supplyManager>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
      orBool Account ==Int TokenOwner
      orBool Account ==Int SupplyManager
      orBool Account ==Int AssetProtectionManager

  // freeze
  rule <k> freeze(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <supplyManager> SupplyManager </supplyManager>
       <frozen> ... (Account |-> _ => Account |-> true) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
      andBool Account =/=Int TokenOwner
      andBool Account =/=Int SupplyManager
      andBool Account =/=Int AssetProtectionManager

  rule <k> freeze(Account, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <supplyManager> SupplyManager </supplyManager>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
      orBool Account ==Int TokenOwner
      orBool Account ==Int SupplyManager
      orBool Account ==Int AssetProtectionManager

  // unfreeze
  rule <k> unfreeze(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <frozen> ... (Account |-> _ => Account |-> false) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  rule <k> unfreeze(_, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)

  // wipe
  rule <k> wipe(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <frozen> ... (Account |-> true) ... </frozen>
       <balances> ... (Account |-> Bal => Account |-> 0) ... </balances>
       <totalSupply> Supply => Supply -Int Bal </totalSupply>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  rule <k> wipe(Account, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <frozen> ... (Account |-> IsFrozen) ... </frozen>
       <balances> ... (Account |-> _) ... </balances>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
      orBool (notBool IsFrozen)

  // isPrivilegedRole
  rule <k> isPrivilegedRole(Account) => true ...</k>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires Account ==Int Owner
      orBool Account ==Int SupplyManager
      orBool Account ==Int AssetProtectionManager

  rule <k> isPrivilegedRole(Account) => false ...</k>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires Account =/=Int Owner
      andBool Account =/=Int SupplyManager
      andBool Account =/=Int AssetProtectionManager

  // increase allowance case: success
  rule <k> increaseAllowance(Spender, Value, { caller : Caller } ) => . ...</k>
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

  // increase allowance case: exception
  rule <k> increaseAllowance(Spender, Value, { caller : Caller } ) => throw ...</k>
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

  // decrease allowance case: success
  rule <k> decreaseAllowance(Spender, Value, { caller : Caller } ) => . ...</k>
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
 
  // decrease allowance: exception
  rule <k> decreaseAllowance(Spender, Value, { caller : Caller } ) => throw ...</k>
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

endmodule

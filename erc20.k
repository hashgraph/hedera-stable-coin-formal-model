/* Ahthor: Grigore Rosu
   Date 2 December 2017

   ERC20-K is a formalization of the informal ERC20 standard at
   https://github.com/ethereum/EIPs/blob/master/EIPS/eip-20-token-standard.md

   See erc20.md for comments.  */

module ERC20-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Value   ::= Int  // this can be changed
  syntax Address ::= Int  // this can be changed
  syntax AExp ::= Value | Address
                | "totalSupply" "(" ")"
                | "owner" "(" ")"
                | "supplyManager" "(" ")"
                | "assetProtectionManager" "(" ")"
                | "proposedOwner" "(" ")"
                | "balanceOf" "(" AExp ")"                             [strict]
                | "allowance" "(" AExp "," AExp ")"                    [strict]
  
  // TODO: some of these will have to move from BExp since the return type has been changed from bool to void
  syntax BExp ::= Bool
                | "constructor" "(" AExp "," AExp "," AExp "," AExp "," AExp "," AExp "," "{" "caller" ":" AExp "}" ")" [strict]
                | "approveAllowance" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                      [strict]
                | "increaseAllowance" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                     [strict]
                | "decreaseAllowance" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                     [strict]
                | "transfer" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                     [strict]
                | "transferFrom" "(" AExp "," AExp "," AExp "," "{" "caller" ":" AExp "}" ")"        [strict]
                | "mint" "(" AExp "," "{" "caller" ":" AExp "}" ")"    [strict]
                | "burn" "(" AExp "," "{" "caller" ":" AExp "}" ")"    [strict]
                | "proposeOwner" "(" AExp "," "{" "caller" ":" AExp "}" ")"    [strict]
                | "claimOwnership" "(""{" "caller" ":" AExp "}" ")"            [strict]
                | "changeSupplyManager" "(" AExp "," "{" "caller" ":" AExp "}" ")"             [strict]
                | "changeAssetProtectionManager" "(" AExp "," "{" "caller" ":" AExp "}" ")"    [strict]
                | "isFrozen" "(" AExp ")"                                           [strict]
                | "isKycPassed" "(" AExp ")"                                        [strict]
                | "setKycPassed" "(" AExp "," "{" "caller" ":" AExp "}" ")"         [strict]
                | "unsetKycPassed" "(" AExp "," "{" "caller" ":" AExp "}" ")"       [strict]
                | "checkTransferAllowed" "(" AExp ")"                               [strict]
                | "freeze" "(" AExp "," "{" "caller" ":" AExp "}" ")"               [strict]
                | "unfreeze" "(" AExp "," "{" "caller" ":" AExp "}" ")"             [strict]
                | "wipe" "(" AExp "," "{" "caller" ":" AExp "}" ")"                 [strict]
                | "isPrivilegedRole" "(" AExp ")"                                   [strict]
                | "initAccount" "(" AExp ")"                                        [strict]
                | "throw"
endmodule

module ERC20
  imports ERC20-SYNTAX
  imports DOMAINS

  configuration <ERC20 unused="true">
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
                </ERC20>

  syntax KResult ::= Int | Bool | String

  syntax Int ::= "MAXVALUE"  [function]
  rule MAXVALUE => 2 ^Int 256 -Int 1

  // propagates exceptions
  rule <k> throw ~> _ => throw </k>

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

  rule <k> balanceOf(Id) => (Balances[Id] orDefault 0) ...</k>
      <balances> Balances:Map  </balances>

  rule <k> owner() => TokenOwner ...</k>
      <tokenOwner> TokenOwner </tokenOwner>

  rule <k> supplyManager() => SupplyManager ...</k>
      <supplyManager> SupplyManager </supplyManager>

  rule <k> assetProtectionManager() => AssetProtectionManager ...</k>
      <assetProtectionManager> AssetProtectionManager </assetProtectionManager>

  rule <k> proposedOwner() => ProposedOwner ...</k>
      <proposedOwner> ProposedOwner </proposedOwner>

  rule <k> isFrozen(Id) => (Frozen[Id] orDefault false) ...</k>
      <frozen> Frozen:Map  </frozen>

  rule <k> isKycPassed(Id) => (KycPassed[Id] orDefault false) ...</k>
      <kycpassed> KycPassed:Map  </kycpassed>

  rule <k> allowance(Allower, Spender) => Value ... </k>
       <allowance>
         <allower> Allower </allower>
         <spenders> ... (Spender |-> Value) ... </spenders>
       </allowance>
  
  rule <k> allowance(_, _) => 0 ... </k>
       [owise]

// helpers

  rule <k> initAccount(Account) => . ...</k>
      <balances> Balances:Map => Balances[Account <- 0] </balances>
      <frozen> Frozen => Frozen[Account <- false] </frozen>
      <kycpassed> KycPassed => KycPassed[Account <- false] </kycpassed>
      <tokenOwner> Owner </tokenOwner>
       <allowances>
       Allowances => 
         Allowances
         <allowance>
           <allower> Account </allower>
           <spenders> (0 |-> 0) </spenders>
         </allowance>
      </allowances>
    requires Owner =/=Int 0

  rule <k> initAccount(_) => throw ...</k> [owise]

// mintable

  // note that according to the spec, the funds go to SupplyManager even if the caller is Owner
  rule <k> mint(Value, { caller : Caller } ) => . ...</k>
       <balances> ... (SupplyManager |-> Balance => SupplyManager |-> Balance +Int Value) ... </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply => Supply +Int Value </totalSupply>
    requires
      Owner =/=Int 0
        andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
        andBool Value >=Int 0
        andBool Supply +Int Value <=Int MAXVALUE

  // NOTE: Kyc or a related function should have a side-effect of initiating balance. Might save a lot of headaches in mint/transfer.
  //       Think we could get rid of this case if so.
  // I could not get K to let me combine this and the above function. The following expression wouldn't parse...
  // Balances [Caller <- (Value +Int (Balances[Caller] orDefault 0))]
  rule <k> mint(Value, { caller : Caller } ) => . ...</k>
       <balances> Balances:Map => Balances [SupplyManager <- Value] </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply => Supply +Int Value </totalSupply>
    requires
      Owner =/=Int 0
        andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
        andBool Value >=Int 0
        andBool Supply +Int Value <=Int MAXVALUE
        andBool notBool (SupplyManager in keys(Balances))

  rule <k> mint(Value, { caller : Caller } ) => throw ...</k>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply </totalSupply>
    requires
      notBool (
        Owner =/=Int 0
        andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
        andBool Value >=Int 0
        andBool Supply +Int Value <=Int MAXVALUE
      )

// burnable
  rule <k> burn(Value, {caller: Caller}) => . ...</k>
       <totalSupply> Supply => Supply -Int Value </totalSupply>
       <balances> ... (SupplyManager |-> OldValue => SupplyManager |-> OldValue -Int Value) ... </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
    requires
      OldValue >=Int Value
      andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
      andBool Value >=Int 0

  rule <k> burn(Value, {caller: Caller}) => throw ...</k>
       <balances> ... (SupplyManager |-> OldValue) ... </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
    requires
      notBool (
        OldValue >=Int Value
        andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
        andBool Value >=Int 0
      )

// compliant

/* // jgorzny: isn't it true that if kyc is set, then account is in frozen?
  // allowed if passed kyc and frozen is unset
  rule <k> checkTransferAllowed(Account) => true ...</k>
      <kycpassed> ... (Account |-> KycPassed) ... </kycpassed>
      <frozen> Frozen:Map </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0
      andBool KycPassed
      andBool (notBool Account in keys(Frozen))
*/

  // allowed if passed kyc and frozen is set to false
  rule <k> checkTransferAllowed(Account) => true ...</k>
      <kycpassed> ... (Account |-> KycPassed) ... </kycpassed>
      <frozen> ... (Account |-> Frozen) ... </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0
      andBool KycPassed
      andBool (notBool Frozen)

  // disallowed if passed kyc is unset or account is frozen
  rule <k> checkTransferAllowed(Account) => false ...</k>
      <kycpassed> KycPassed:Map </kycpassed>
      <frozen> ... (Account |-> Frozen) ... </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool (notBool Account in keys(KycPassed))
      orBool Frozen

  // disallowed if passed kyc is set to false or account is frozen
  rule <k> checkTransferAllowed(Account) => false ...</k>
      <kycpassed> ... (Account |-> KycPassed) ... </kycpassed>
      <frozen> ... (Account |-> Frozen) ... </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool (notBool KycPassed)
      orBool Frozen

// delegable
  // Note: In the high-level spec, approveAllowance() has no restrictions regarding checkTransferAllowed()

  // approve case: caller in outer map, update spender in inner map, success
  rule <k> approveAllowance(Spender, Value, { caller : Caller } ) => . ...</k>
       <allowances> 
         ...
         <allowance>
           <allower> Caller </allower>
           <spenders> ... (Spender |-> _ => Spender |-> Value) ... </spenders>
         </allowance>
         ...
       </allowances>
    requires Value >=Int 0

  // approve case: caller in outer map, spender not in inner map, success
  rule <k> approveAllowance(Spender, Value, { caller : Caller } ) => . ...</k>
       <allowance>
         <allower> Caller </allower>
         <spenders> Spenders => Spenders (Spender |-> Value) </spenders>
       </allowance>

  // approve case: insufficient value, fail
  rule <k> approveAllowance(_, Value, { caller : _ }) => throw ...</k>
    requires Value <Int 0

  // approve case: caller not in outer map
  rule <k> approveAllowance(Spender, Value, { caller : Caller } ) => . ...</k>
       <allowances> 
         (.Bag =>
           <allowance>
             <allower> Caller </allower>
             <spenders> (Spender |-> Value) </spenders>
           </allowance>
         )
         ...
       </allowances>
    [owise]

// transferable
  // Note: I do not check for (TokenOwner =/= 0) since (Kyc == true) => (TokenOwner =/= 0)
 
  // transfer case: To =/= From, success 
  rule <k> transfer(To, Value, { caller : From } ) => . ...</k>
      // Note: this map update will not work correctly if From == To (it will effectively mint tokens)
       <balances> Balances:Map => Balances[From <- ({Balances[From]}:>Int -Int Value)][To <- ({Balances[To]}:>Int +Int Value)] </balances>  
       <kycpassed> ... (To |-> true) (From |-> true) ... </kycpassed>
       <frozen> ... (To |-> false) (From |-> false) ... </frozen>
    requires To =/=Int From
      andBool Value >=Int 0
      andBool {Balances[From]}:>Int >=Int Value

  // transfer case: To == From, success 
  rule <k> transfer(Account, Value, { caller : Account } ) => . ...</k>
       <balances> ... (Account |-> Balance) ... </balances>  
       <kycpassed> ... (Account |-> true) ... </kycpassed>
       <frozen> ... (Account |-> false) ... </frozen>
    requires Value >=Int 0
      andBool Balance >=Int Value

  // TODO: I think the below transfer() cases are likely incomplete; 
  //       might be able to remove all failing cases in favor of an [owise] as in transferFrom()
  // Maybe: rule <k> transfer(To, Value, { caller : From } ) => throw ...</k> [owise]

  // transfer case: To=/=From, To and From in maps, basic condition does not hold, fail
  rule <k> transfer(To, Value, { caller : From } ) => throw ...</k>
       <balances> ... (From |-> Balance) ... </balances>  
       <kycpassed> ... (To |-> ToKyc) (From |-> FromKyc) ... </kycpassed>
       <frozen> ... (To |-> ToFrozen) (From |-> FromFrozen) ... </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires notBool (To =/=Int From
      andBool Value >=Int 0
      andBool Balance >=Int Value
      andBool TokenOwner =/=Int 0
      andBool ToKyc
      andBool FromKyc
      andBool notBool (ToFrozen)
      andBool notBool (FromFrozen)
    )

  // transfer case: To=/=From, To or From not in a map, fail
  rule <k> transfer(To, _, { caller : From } ) => throw ...</k>
       <balances> Balances </balances>  
       <kycpassed> KycPassed </kycpassed>
       <frozen> Frozen </frozen>
    requires notBool (
      To in keys(Balances)
      andBool From in keys(Balances)
      andBool To in keys(KycPassed)
      andBool From in keys(KycPassed)
      andBool To in keys(Frozen)
      andBool From in keys(Frozen)
    )

  // transfer case: To == From, basic condition does not hold, fail
    rule <k> transfer(Account, Value, { caller : Account } ) => throw ...</k>
       <balances> ... (Account |-> Balance) ... </balances>  
       <kycpassed> ... (Account |-> AccountKyc) ... </kycpassed>
       <frozen> ... (Account |-> AccountFrozen) ... </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires notBool ( Value >=Int 0 
      andBool Balance >=Int Value
      andBool TokenOwner =/=Int 0
      andBool AccountKyc
      andBool notBool (AccountFrozen)
    )

  // transfer case: To == From, Account not in a map, fail
  rule <k> transfer(Account, _, { caller : Account } ) => throw ...</k>
       <balances> Balances </balances>  
       <kycpassed> KycPassed </kycpassed>
       <frozen> Frozen </frozen>
    requires notBool (
      Account in keys(Balances)
      andBool Account in keys(KycPassed)
      andBool Account in keys(Frozen)
    )

  // transferFrom case: To =/= From, success
  rule <k> transferFrom(From, To, Value, {caller: Caller}) => . ... </k>
       <allowance>
         <allower> From </allower>
         <spenders> ... (Caller |-> (Allowance => (Allowance -Int Value))) ... </spenders>
       </allowance>
       <balances> Balances:Map => Balances[From <- ({Balances[From]}:>Int -Int Value)][To <- ({Balances[To]}:>Int +Int Value)] </balances>  
       <kycpassed> ... (To |-> true) (From |-> true) (Caller |-> true) ... </kycpassed>
       <frozen> ... (To |-> false) (From |-> false) (Caller |-> false) ... </frozen>
    requires To =/=Int From
      andBool Value >=Int 0
      andBool {Balances[From]}:>Int >=Int Value
      andBool Allowance >=Int Value

  // transferFrom case: To == From, success
  rule <k> transferFrom(From, From, Value, {caller: Caller}) => . ... </k>
       <allowance>
         <allower> From </allower>
         // still subtracting from allowance even though no funds actually moved
         <spenders> ... (Caller |-> (Allowance => (Allowance -Int Value))) ... </spenders>
       </allowance>
       <balances> Balances:Map </balances>  
       <kycpassed> ... (From |-> true) (Caller |-> true) ... </kycpassed>
       <frozen> ... (From |-> false) (Caller |-> false) ... </frozen>
    requires Value >=Int 0
      andBool {Balances[From]}:>Int >=Int Value
      andBool Allowance >=Int Value

  // transferFrom case: fail otherwise
  rule <k> transferFrom(_, _, _, {caller: _}) => throw ... </k> [owise]

// privileged roles

  rule <k> proposeOwner(ProposedOwner, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <proposedOwner> _ => ProposedOwner </proposedOwner>
    requires Caller =/=Int 0
      andBool ProposedOwner =/=Int 0

  rule <k> proposeOwner(_, { caller : _ } ) => throw ...</k> [owise]

  rule <k> claimOwnership( { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner => Caller </tokenOwner>
       <proposedOwner> Caller => 0 </proposedOwner>
    requires Caller =/=Int 0
      andBool TokenOwner =/=Int 0

  rule <k> claimOwnership( { caller : _ } ) => throw ...</k> [owise]

  rule <k> changeSupplyManager(SupplyManager, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <supplyManager> _ => SupplyManager </supplyManager>
    requires Caller =/=Int 0
      andBool SupplyManager =/=Int 0

  rule <k> changeSupplyManager(_, { caller : _ } ) => throw ...</k> [owise]

  rule <k> changeAssetProtectionManager(AssetProtectionManager, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <assetProtectionManager> _ => AssetProtectionManager </assetProtectionManager>
    requires Caller =/=Int 0
      andBool AssetProtectionManager =/=Int 0

  rule <k> changeAssetProtectionManager(_, { caller : _ } ) => throw ...</k> [owise]

// unclassified

  // case: Account already in map, success
  rule <k> setKycPassed(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <kycpassed> ... (Account |-> false => Account |-> true) ... </kycpassed>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
  
  // case: Account kyc already true or Caller incorrect, fail
  /* This can replace the owise with the initAccount approach
  rule <k> setKycPassed(Account, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <kycpassed> ... (Account |-> Passed) ... </kycpassed>
    requires notBool (
      TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
      andBool notBool(Passed)
    )
  */ 
  rule <k> setKycPassed(_, { caller : _ } ) => throw ...</k> [owise]
  
  // unset kycpassed
  rule <k> unsetKycPassed(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <kycpassed> ... (.Map => Account |-> false) ... </kycpassed>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  rule <k> unsetKycPassed(_, { caller : _ } ) => throw ...</k> [owise]

  // freeze
  rule <k> freeze(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <frozen> ... (.Map => Account |-> true) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  rule <k> freeze(_, { caller : _ } ) => throw ...</k> [owise]

  // unfreeze
  rule <k> unfreeze(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <frozen> ... (.Map => Account |-> false) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  rule <k> unfreeze(_, { caller : _ } ) => throw ...</k> [owise]

  // wipe
  rule <k> wipe(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <frozen> ... (Account |-> true) ... </frozen>
       <balances> ... (Account |-> Bal => Account |-> 0) ... </balances>
       <totalSupply> Supply => Supply -Int Bal </totalSupply>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  rule <k> wipe(_, { caller : _ } ) => throw ...</k> [owise]

  // isPrivilegedRole
  rule <k> isPrivilegedRole(Account) => true ...</k>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires Account ==Int Owner
      orBool Account ==Int SupplyManager
      orBool Account ==Int AssetProtectionManager

  rule <k> isPrivilegedRole(_) => false ...</k> [owise]

  // increase allowance case: caller in outer map, update spender in inner map, success
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
    requires TokenOwner =/=Int 0
      andBool Value >=Int 0
      andBool (OldAllowance +Int Value) <=Int MAXVALUE
      andBool OldAllowance >=Int 0

  // increase allowance case: caller in outer map, spender not in inner map, success
  rule <k> increaseAllowance(Spender, Value, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <allowance>
         <allower> Caller </allower>
         <spenders> Spenders => Spenders (Spender |-> Value) </spenders>
       </allowance>
    requires TokenOwner =/=Int 0
      andBool Value >=Int 0
      andBool notBool (Spender in keys(Spenders))

  // increase allowance case: caller not in outer map
  rule <k> increaseAllowance(Spender, Value, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <allowances> 
         (.Bag =>
           <allowance>
             <allower> Caller </allower>
             <spenders> (Spender |-> Value) </spenders>
           </allowance>
         )
         ...
       </allowances>
    requires TokenOwner =/=Int 0
      andBool Value >=Int 0
 
  // increase allowance case: insufficient value, fail
  rule <k> increaseAllowance(_, _, { caller : _ }) => throw ...</k> [owise]

  // decrease allowance case: caller in outer map, update spender in inner map, success
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
    requires TokenOwner =/=Int 0
      andBool Value >=Int 0
      andBool (OldAllowance -Int Value) >=Int 0
      andBool OldAllowance >=Int 0
 
  // decrease allowance: all other cases
  rule <k> decreaseAllowance(_, _, { caller : _ }) => throw ...</k> [owise]

endmodule

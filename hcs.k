module HCS-SYNTAX
  imports DOMAINS-SYNTAX

  // Syntax module provides concrete syntax for token functions.
  // It allows for testing the specification, thus making it executable.

  syntax Value   ::= Int  // this can be changed
  syntax Address ::= Int  // this can be changed
  syntax AExp ::= Value | Address
                | "name" "(" ")"                                                                                        [strict]
                | "symbol" "(" ")"                                                                                      [strict]
                | "decimals" "(" ")"                                                                                    [strict]
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

  // This module defines semantics of the token.

  // Configuration specifies a list of fields over which functions operate.
  configuration <HCS unused="true">
                  <k> $PGM:K </k>
                  // balances maps each address to the number of tokens it possess.
                  <balances>
                    .Map
                  </balances>
                  // frozen maps each address to a boolean value indicating whether the address is frozen.
                  <frozen>
                    .Map
                  </frozen>
                  // kycpassed maps each address to a boolean value indicating whether the address passed the KYC.
                  <kycpassed>
                    .Map
                  </kycpassed>
                  // allowances maps each address to a map which maps each spender to the approved amount of tokens
                  // that they may spend on behalf of the allower.
                  <allowances>
                    <allowance multiplicity="*" type="Map"> // Allower |-> Spenders
                      <allower> 0 </allower>
                      <spenders type="Map"> .Map </spenders> // Spender |-> Amount
                    </allowance>
                  </allowances>
                  // tokenName indicates name of the token. Here modeled as integer for simplcity.
                  <tokenName> 0 </tokenName>
                  // tokenSymbol indicates symbol of the token. Here modeled as integer for simplcity.
                  <tokenSymbol> 0 </tokenSymbol>
                  // tokenDecimal indicates that one unit of the token can be subdivided into 10 to the power of tokenDecimal subunits.
                  <tokenDecimal> 0 </tokenDecimal>
                  // totalSupply indicates the total number of tokens.
                  <totalSupply> 0 </totalSupply>
                  // tokenOwner is the address of token contract owner.
                  <tokenOwner> 0 </tokenOwner>
                  // supplyManager is the address of token supply manager. They can mint and burn tokens.
                  <supplyManager> 0 </supplyManager>
                  // assetProtectionManager is the address of asset protection manager. They are responsible for KYC and account freezing.
                  <assetProtectionManager> 0 </assetProtectionManager>
                  // proposedOwner is a new owner proposed by the current token contract owner.
                  <proposedOwner> 0 </proposedOwner>
                </HCS>

  syntax KResult ::= Int | Bool | String

// MAXVALUE is used to model max integer value to avoid overflows.
  syntax Int ::= "MAXVALUE"  [function]
  rule MAXVALUE => 2 ^Int 256 -Int 1

// base

  /*
    Constructor initializes the token contract.

    Pre-conditions
        * Owner = 0x // the existing Owner has not been set
        * tokenDecimal >= 0
        * totalSupply >= 0
        * caller != 0x // the newly created Owner is non-zero
        * supplyManager != 0x
        * assetProtectionManager != 0x

    Post-conditions
        * TokenName = tokenName
        * TokenSymbol = tokenSymbol
        * TokenDecimal = tokenDecimal
        * TotalSupply = totalSupply
        * Owner = caller
        * SupplyManager = supplyManager
        * AssetProtectionManager = assetProtectionManager
        * Balances = { SupplyManager->TotalSupply } // SupplyManager gets the TotalSupply of tokens
        * Allowances = {}
        * Frozen = {} // no account is frozen by default
        * KycPassed = { Owner->true, SupplyManager->true, AssetProtectionManager->true }
        * ProposedOwner = 0x
   */
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

  /*
    Get token name.

    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = TokenName
   */
  rule <k> name() => Name ...</k>
       <tokenName> Name </tokenName>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> name() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Get token symbol.

    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = TokenSymbol
   */
  rule <k> symbol() => Symbol ...</k>
       <tokenSymbol> Symbol </tokenSymbol>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> symbol() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Get token decimal.

    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = TokenDecimal
   */
  rule <k> decimals() => Decimals ...</k>
       <tokenDecimal> Decimals </tokenDecimal>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> decimals() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Get total supply.

    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = TotalSupply  
   */
  rule <k> totalSupply() => Total ...</k>
       <totalSupply> Total </totalSupply>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> totalSupply() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Get account’s balance

    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = Balances[addr]
   */
  rule <k> balanceOf(Id) => (Balances[Id] orDefault 0) ...</k>
       <balances> Balances:Map </balances>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> balanceOf(_) => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Get owner

    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = Owner
   */
  rule <k> owner() => TokenOwner ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> owner() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Get supply manager

    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = SupplyManager
  */
  rule <k> supplyManager() => SupplyManager ...</k>
       <supplyManager> SupplyManager </supplyManager>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> supplyManager() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Get asset protection manager

    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = AssetProtectionManager
  */
  rule <k> assetProtectionManager() => AssetProtectionManager ...</k>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> assetProtectionManager() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Get proposed owner

    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = ProposedOwner
  */
  rule <k> proposedOwner() => ProposedOwner ...</k>
       <proposedOwner> ProposedOwner </proposedOwner>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> proposedOwner() => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Is account frozen

    Pre-conditions
        * Owner != 0x
    Post-conditions
        * result = Frozen[addr]
  */
  rule <k> isFrozen(Id) => (Frozen[Id] orDefault false) ...</k>
       <frozen> Frozen:Map </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> isFrozen(_) => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Did the account pass KYC/AML

    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = KycPassed[addr]
  */
  rule <k> isKycPassed(Id) => (KycPassed[Id] orDefault false) ...</k>
       <kycpassed> KycPassed:Map </kycpassed>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // throws if there is no owner
  rule <k> isKycPassed(_) => throw ...</k>
       <tokenOwner> 0 </tokenOwner>

  /*
    Get account’s allowance

    Pre-conditions
        * Owner != 0x
    Post-conditions
        * result = Allowances[addr][spender]
  */
  rule <k> allowance(Allower, Spender) => Value ... </k>
       <allowance>
         <allower> Allower </allower>
         <spenders> ... (Spender |-> Value) ... </spenders>
       </allowance>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0
  
  // throws if there is no owner
  rule <k> allowance(_, _) => throw ... </k>
       <tokenOwner> 0 </tokenOwner>

// mintable

  /*
    Mint

    Pre-conditions
        * Owner != 0x // constructor has been called
        * caller = SupplyManager || caller = Owner
        * value >= 0
        * TotalSupply + value <= MAX_INT // prevents overflow
        * TotalSupply >= Balances[SupplyManager]

    Post-conditions
        * TotalSupply’ = TotalSupply + value // the new supply is increased by value
        * Balances[SupplyManager]’ = Balances[SupplyManager] + value

    Note that according to the spec, the funds go to SupplyManager even if the caller is Owner.
   */
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

  // throws if pre-conditions are not satisfied
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

  /*
    Burn
    
    Pre-conditions
        * Owner != 0x
        * caller = SupplyManager || caller = Owner
        * value >= 0
        * Balances[SupplyManager] >= value
        * TotalSupply >= Balances[SupplyManager]

    Post-conditions
        * TotalSupply’ = TotalSupply - value // the new supply is decreased by value
        * Balances[SupplyManager]’ = Balances[SupplyManager] - value
   */
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

  // throws if pre-conditions are not satisfied
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

  /*
    Detect transfer restriction
    
    Pre-conditions
        * Owner != 0x

    Post-conditions
        * result = (!Frozen[addr] && KycPassed[addr])
   */
  rule <k> checkTransferAllowed(Account) => true ...</k>
      <kycpassed> ... (Account |-> true) ... </kycpassed>
      <frozen> ... (Account |-> false) ... </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0

  // transfer disallowed otherwise
  rule <k> checkTransferAllowed(Account) => false ...</k>
      <kycpassed> ... (Account |-> KycPassed) ... </kycpassed>
      <frozen> ... (Account |-> Frozen) ... </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool (notBool KycPassed)
      orBool Frozen

// delegable

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

  // throws if pre-conditions are not satisfied
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

  /*
    Transfer
    
    Pre-conditions
        * Owner != 0x
        * value >= 0
        * Balances[caller] >= value
        * CheckTransferAllowed(caller)
        * CheckTransferAllowed(to)

    Post-conditions
        * Balances[caller]’ = Balances[caller] - value
        * Balances[to]' = Balances[to] + value
   */
 
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

  // throws if pre-conditions are not satisfied
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

  /*
    Transfer tokens on behalf of the owner
    
    Pre-conditions
        * Owner != 0x
        * value >= 0
        * Balances[from] >= value
        * Allowances[from][caller] >= value
        * CheckTransferAllowed(caller)
        * CheckTransferAllowed(from)
        * CheckTransferAllowed(to)

    Post-conditions
        * Balances[from]’ = Balances[from] - value
        * Allowances[from][caller]’ = Allowances[from][caller] - value
        * Balances[to]’ = Balances[to] + value
   */

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

  // throws if pre-conditions are not satisfied
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

  /*
    ProposeOwner
    
    Pre-conditions
        * Owner != 0x
        * caller = Owner
        * addr != 0x
        * CheckTransferAllowed(addr)

    Post-conditions
        * ProposedOwner = addr
   */
  rule <k> proposeOwner(ProposedOwner, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <proposedOwner> _ => ProposedOwner </proposedOwner>
       <kycpassed> ... (ProposedOwner |-> true) ... </kycpassed>
       <frozen> ... (ProposedOwner |-> false) ... </frozen>
    requires Caller =/=Int 0 andBool ProposedOwner =/=Int 0

  // throws if pre-conditions are not satisfied
  rule <k> proposeOwner(ProposedOwner, { caller : Caller } ) => throw ...</k>
       <kycpassed> ... (ProposedOwner |-> KycPassed) ... </kycpassed>
       <frozen> ... (ProposedOwner |-> Frozen) ... </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool TokenOwner =/=Int Caller
      orBool ProposedOwner ==Int 0
      orBool (notBool KycPassed)
      orBool Frozen

  /*
    Claim ownership
    
    Pre-conditions
        * Owner != 0x
        * caller = ProposedOwner
        * CheckTransferAllowed(caller)

    Post-conditions
        * Owner = caller
        * ProposedOwner = 0x
   */
  rule <k> claimOwnership( { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner => Caller </tokenOwner>
       <proposedOwner> Caller => 0 </proposedOwner>
       <kycpassed> ... (Caller |-> true) ... </kycpassed>
       <frozen> ... (Caller |-> false) ... </frozen>
    requires Caller =/=Int 0 andBool TokenOwner =/=Int 0

  // throws if pre-conditions are not satisfied
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

  /*
    ChangeSupplyManager
    
    Pre-conditions
        * Owner != 0x
        * caller = Owner
        * addr != 0x
        * CheckTransferAllowed(addr)

    Post-conditions
        * SupplyManager = addr
   */
  rule <k> changeSupplyManager(SupplyManager, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <supplyManager> _ => SupplyManager </supplyManager>
       <kycpassed> ... (SupplyManager |-> true) ... </kycpassed>
       <frozen> ... (SupplyManager |-> false) ... </frozen>
    requires Caller =/=Int 0 andBool SupplyManager =/=Int 0

  // throws if pre-conditions are not satisfied
  rule <k> changeSupplyManager(SupplyManager, { caller : Caller } ) => throw ...</k>
       <kycpassed> ... (SupplyManager |-> KycPassed) ... </kycpassed>
       <frozen> ... (SupplyManager |-> Frozen) ... </frozen>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool SupplyManager ==Int 0
      orBool Caller =/=Int TokenOwner 
      orBool (notBool KycPassed)
      orBool Frozen

  /*
    ChangeAssetProtectionManager

    Pre-conditions
        * Owner != 0x
        * caller = Owner
        * addr != 0x
        * CheckTransferAllowed(addr)

    Post-conditions
        * AssetProtectionManager = addr
   */
  rule <k> changeAssetProtectionManager(AssetProtectionManager, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <assetProtectionManager> _ => AssetProtectionManager </assetProtectionManager>
       <kycpassed> ... (AssetProtectionManager |-> true) ... </kycpassed>
       <frozen> ... (AssetProtectionManager |-> false) ... </frozen>
    requires Caller =/=Int 0 andBool AssetProtectionManager =/=Int 0

  // throws if pre-conditions are not satisfied
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

  /*
    Set KYC passed
    
    Pre-conditions
        * Owner != 0x
        * caller = AssetProtectionManager || caller = Owner

    Post-conditions
        * KycPassed[addr]
   */
  rule <k> setKycPassed(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <kycpassed> ... (Account |-> _ => Account |-> true) ... </kycpassed>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
  
  // throws if pre-conditions are not satisfied
  rule <k> setKycPassed(_, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)
  
  /*
    Unset passed KYC
    
    Pre-conditions
        * Owner != 0x
        * caller = AssetProtectionManager || caller = Owner
        * !isPrivilegedRole(addr)

    Post-conditions
        * !KycPassed[addr]
   */
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

  // throws if pre-conditions are not satisfied
  rule <k> unsetKycPassed(Account, { caller : Caller } ) => throw ...</k>
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

  // throws if pre-conditions are not satisfied
  rule <k> freeze(Account, { caller : Caller } ) => throw ...</k>
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
  rule <k> unfreeze(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <frozen> ... (Account |-> _ => Account |-> false) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  // throws if pre-conditions are not satisfied
  rule <k> unfreeze(_, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)

  /*
    Wipe
    
    Pre-conditions
        * Owner != 0x
        * caller = AssetProtectionManager || caller = Owner
        * Frozen[addr]

    Post-conditions
        * TotalSupply’ = TotalSupply - Balances[addr] // total supply decreased
        * Balances[addr]’ = 0 // balance “updated” to 0
   */
  rule <k> wipe(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <frozen> ... (Account |-> true) ... </frozen>
       <balances> ... (Account |-> Bal => Account |-> 0) ... </balances>
       <totalSupply> Supply => Supply -Int Bal </totalSupply>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  // throws if pre-conditions are not satisfied
  rule <k> wipe(Account, { caller : Caller } ) => throw ...</k>
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

    Post-conditions
        * result = (addr = Owner || addr = AssetProtectionManager || addr = SupplyManager)
   */
  rule <k> isPrivilegedRole(Account) => true ...</k>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires Account ==Int Owner
      orBool Account ==Int SupplyManager
      orBool Account ==Int AssetProtectionManager

  // false if pre-conditions are not satisfied
  rule <k> isPrivilegedRole(Account) => false ...</k>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires Account =/=Int Owner
      andBool Account =/=Int SupplyManager
      andBool Account =/=Int AssetProtectionManager

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

  // throws if pre-conditions are not satisfied
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
 
  // throws if pre-conditions are not satisfied
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

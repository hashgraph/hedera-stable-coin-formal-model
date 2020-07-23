requires "erc20.k"

module UNCLASSIFIED-SPEC
  imports ERC20

  // correctness of `setKycPassed` - changing from false to true
  rule
      <k>
          setKycPassed(Target:Int, {caller: Caller})
        =>
          .
      ...</k>
         <tokenOwner> Owner </tokenOwner>
         <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
         <kycpassed> ... (Target |-> false => Target |-> true) ... </kycpassed>
      requires
        Owner =/=Int 0
          andBool Caller =/=Int 0
          andBool (Caller ==Int AssetProtectionManager orBool Caller ==Int Owner)

  // correctness of `setKycPassed` - throw case (already true)
  rule
      <k>
          setKycPassed(Target:Int, {caller: Caller})
        =>
          throw
      ...</k>
         <tokenOwner> Owner </tokenOwner>
         <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
         <kycpassed> ... (Target |-> true) ... </kycpassed>
      requires
        Owner =/=Int 0
          andBool Caller =/=Int 0
          andBool (Caller ==Int AssetProtectionManager orBool Caller ==Int Owner)

  // correctness of `setKycPassed` - throw case (wrong caller)
  rule
      <k>
          setKycPassed(Target:Int, {caller: Caller})
        =>
          throw
      ...</k>
         <tokenOwner> Owner </tokenOwner>
         <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
         <kycpassed> ... (Target |-> _) ... </kycpassed>
      requires
        Owner =/=Int 0
          andBool Caller =/=Int 0
          andBool (Caller =/=Int AssetProtectionManager andBool Caller =/=Int Owner)

  // correctness of `unsetKycPassed` - good case
  rule
      <k>
          unsetKycPassed(Target:Int, {caller: Caller})
        =>
          .
      ...</k>
        <tokenOwner> TokenOwner </tokenOwner>
        <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
        <kycpassed> ... (Target |-> true => Target |-> false) ... </kycpassed>
      requires TokenOwner =/=Int 0
        andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  // correctness of `unsetKycPassed` - throw if wrong person unsets
  rule
      <k>
        unsetKycPassed(Target:Int, {caller: Caller})
      =>
        throw
      ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <kycpassed> ... (Target |-> _) ... </kycpassed> // jgorzny would like to drop this.
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)

  // correctness of `unsetKycPassed` - throw case (already false)
  rule
      <k>
          unsetKycPassed(Target:Int, {caller: Caller})
      =>
          throw
      ...</k>
        <tokenOwner> Owner </tokenOwner>
        <kycpassed> ... (Target |-> false) ... </kycpassed>
      requires
        Owner =/=Int 0
          andBool Caller =/=Int 0

  // correctness of `freeze` - update
  rule <k>
          freeze(Account:Int, {caller: Caller})
       =>
          .
      ...</k>
        <tokenOwner> TokenOwner </tokenOwner>
        <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
        <frozen> ... (Account |-> false => Account |-> true) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  // correctness of `freeze` - bad caller
  rule <k>
          freeze(Account:Int, { caller : Caller } )
       =>
          throw
      ...</k>
        <tokenOwner> TokenOwner </tokenOwner>
        <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
        <frozen> ... (Account |-> _) ... </frozen>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)


  // correctness of `freeze` - already true
  rule
      <k>
          freeze(Account:Int, {caller: Caller})
      =>
          throw
      ...</k>
        <tokenOwner> Owner </tokenOwner>
        <frozen> ... (Account |-> true) ... </frozen>
      requires
        Owner =/=Int 0
          andBool Caller =/=Int 0

// correctness of `unfreeze` - update
rule <k>
        unfreeze(Account:Int, {caller: Caller})
     =>
        .
    ...</k>
      <tokenOwner> TokenOwner </tokenOwner>
      <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
      <frozen> ... (Account |-> true => Account |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)


// correctness of `unfreeze` - bad caller
rule <k>
        unfreeze(Account:Int, {caller: Caller})
     =>
        throw
    ...</k>
      <tokenOwner> TokenOwner </tokenOwner>
      <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
      <frozen> ... (Account |-> _) ... </frozen>
  requires TokenOwner ==Int 0
    orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)


// correctness of `unfreeze` - already false
rule
    <k>
        unfreeze(Account:Int, {caller: Caller})
    =>
        throw
    ...</k>
      <tokenOwner> Owner </tokenOwner>
      <frozen> ... (Account |-> false) ... </frozen>
    requires
      Owner =/=Int 0
        andBool Caller =/=Int 0

  // correctness of `wipe` - update
  rule <k>
          freeze(Account:Int, {caller: Caller})
          ~>
          wipe(Account, {caller: Caller})
      =>
          .
      ...</k>
        <tokenOwner> TokenOwner </tokenOwner>
        <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
        <frozen> ... (Account |-> false => Account |-> true) ... </frozen>
        <balances> ... (Account |-> Bal => Account |-> 0) ... </balances>
        <totalSupply> Supply => Supply -Int Bal </totalSupply>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  // correctness of `wipe` - bad caller
  rule <k>
          wipe(Account:Int, {caller: Caller})
      =>
          throw
      ...</k>
        <tokenOwner> TokenOwner </tokenOwner>
        <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
        <totalSupply> _Supply </totalSupply>
        <frozen> ... (Account |-> _) ... </frozen>
        <balances> ... (Account |-> _) ... </balances>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)

  // correctness of `wipe` - account not frozen
  rule <k>
          wipe(Account:Int, {caller: Caller})
      =>
          throw
      ...</k>
        <tokenOwner> TokenOwner </tokenOwner>
        <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
        <totalSupply> _Supply </totalSupply>
        <frozen> ... (Account |-> false) ... </frozen>
        <balances> ... (Account |-> _) ... </balances>
    requires TokenOwner =/=Int 0
      andBool (Caller =/=Int TokenOwner orBool Caller =/=Int AssetProtectionManager)

  // correctness of `isPrivilegedRole` - true
  rule <k>
          isPrivilegedRole(Account:Int)
      =>
          true
      ...</k>
        <tokenOwner> TokenOwner </tokenOwner>
        <supplyManager> SupplyManager </supplyManager>
        <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires (TokenOwner =/=Int 0 orBool AssetProtectionManager =/=Int 0 orBool SupplyManager =/=Int 0)
      andBool (Account ==Int TokenOwner orBool Account ==Int AssetProtectionManager
      orBool Account ==Int SupplyManager)


  // correctness of `isPrivilegedRole` - false
  rule <k>
          isPrivilegedRole(Account:Int)
      =>
          false
      ...</k>
        <tokenOwner> TokenOwner </tokenOwner>
        <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
        <supplyManager> SupplyManager </supplyManager>
    requires notBool(Account ==Int TokenOwner
      orBool Account ==Int AssetProtectionManager orBool Account ==Int SupplyManager)

endmodule

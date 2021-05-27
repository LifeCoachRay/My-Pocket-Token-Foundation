pragma solidity ^0.4.21;
library SafeMath {
    function add(uint a, uint b) internal pure returns (uint c) {
        c = a + b;
        require(c >= a);
    }
    function sub(uint a, uint b) internal pure returns (uint c) {
        require(b <= a);
        c = a - b;
    }
    function mul(uint a, uint b) internal pure returns (uint c) {
        c = a * b;
        require(a == 0 || c / a == b);
    }
    function div(uint a, uint b) internal pure returns (uint c) {
        require(b > 0);
        c = a / b;
    }
}

contract MyContract{
    using SafeMath for uint256;

    uint public price;
    uint public mult_dec;
    mapping(address => uint) public balances;

    function MyContract() public {
        price = 1000000000000000000;
        mult_dec = 10**18;
    }

    function sellTokens(uint256 amountTokens) public {
        balances[msg.sender] = balances[msg.sender].sub(amountTokens);
        uint amountEther = amountTokens.mul(price).div(mult_dec);
        msg.sender.transfer(amountEther);
    }

    function buyTokens() public payable{
        uint numberofTokens = msg.value.mul(mult_dec).div(price);        
        require(numberofTokens>0);
        balances[msg.sender] = balances[msg.sender].add(numberofTokens); 
    }



}

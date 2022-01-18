//SPDX-License-Identifier: Unlicense
pragma solidity ^0.8.11;

import '@openzeppelin/contracts/token/ERC721/extensions/ERC721Pausable.sol';
import '@openzeppelin/contracts/access/Ownable.sol';
import '@openzeppelin/contracts/utils/math/SafeMath.sol';


contract TagNFT is ERC721Pausable , Ownable {
    using SafeMath for uint256; 

    mapping ( address => bool ) private  allowedContracts;

    uint256 private counter;

    mapping ( bytes32 => trackStruct ) public tracker;

    struct trackStruct{
        string TAGName;
        uint256 counter;
    }

    modifier onlyAllowedContract (){
        require(allowedContracts[msg.sender] == true);
        _;
    }

    modifier isUnique (string memory _id){
        bytes32 hash = keccak256(abi.encodePacked(_id));
        require(tracker[hash].counter == 0);
        _;
    }

    event mintEvent( string  _id , bytes32 _hash , uint256 _counter );

    constructor ( string memory _name, string memory _symbol ) ERC721( _name , _symbol ) Ownable()  { }

    function pauseToken () onlyOwner public view {
        _pause;
    }

    function unpauseToken () onlyOwner public view {
        _unpause;
    }

    function allowContract ( address _addr ) onlyOwner public returns ( bool ) {
        allowedContracts[_addr ] = true;
        return true;
    }

    function disallowContract ( address _addr ) onlyOwner public returns ( bool ) {
        allowedContracts[_addr ] = false;
        return true;
    }

    
    

    function mintTokens( address to, string memory tokenDetails ) onlyAllowedContract isUnique(tokenDetails) public returns ( bool ){
        counter = counter.add( 1 );
        bytes32 hash = keccak256(abi.encodePacked(tokenDetails));
        tracker[hash] = trackStruct( tokenDetails , counter );
        _safeMint( to , counter );
        //_setTokenURI( counter , tokenDetails );
        emit mintEvent( tokenDetails , hash , counter);
        return true;
    }

    function burnTokens( uint256 id ) onlyOwner public returns ( bool ){
        _burn( id );
        return true;
    }

    function transfer( address to , uint256 id ) onlyOwner public returns ( bool ){
        _transfer( msg.sender , to , id );
        return true;
    }

}

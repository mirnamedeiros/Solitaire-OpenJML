/*******************************************************************************
 * Solitaire
 *  
 *  Copyright (C) 2016 by Martin P. Robillard
 *  
 *  See: https://github.com/prmr/Solitaire
 *  
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *  
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *  
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see http://www.gnu.org/licenses/.
 *******************************************************************************/
package ca.mcgill.cs.stg.solitaire.cards;

import java.util.ArrayList;

/**
 * An immutable description of a playing card. This abstraction
 * is designed to be independent of game logic, so it does
 * not provide any service that relies on the knowledge
 * of the rules of any particular game.
 * 
 * This class implements the Flyweight design pattern: 
 * there can only ever be one instance of a card that 
 * represents a specific real-world playing card (such as ace
 * of spaces). In the absence of serialization and reflection,
 * this ensures that the behavior of the == operator is identical 
 * to that of the equals method when two card arguments are 
 * provided.
 */
public final class Card
{
	//@ public invariant CARDS != null;
	// Indexed by suit, then rank
	//@ spec_public
	private static final ArrayList<ArrayList<Card>> CARDS = new ArrayList<>();

    static {
		//@ ghost int index = 0;
		//@ maintaining 0 <= \count < Rank.values().length;
		//@ maintaining \forall int k; 0 <= k < \count; CARDS.get(k) != null && CARDS.get(k).size() == Rank.values().length;
		//@ loop_writes CARDS;
		//@ decreases CARDS.size() - \count;	
        for (Suit suit : Suit.values()) {
            ArrayList<Card> suitList = new ArrayList<>();

			//@ maintaining 0 <= \count < Rank.values().length;
			//@ maintaining \forall int k; 0 <= k < \count; CARDS.get(index).get(k) != null;
			//@ loop_writes CARDS;
			//@ decreases CARDS.get(index).size() - \count;
            for (Rank rank : Rank.values()) {
                suitList.add(new Card(rank, suit));
            }
			//@ set index = index + 1;
            CARDS.add(suitList);
        }
    }

	//@ spec_public
    private final Rank aRank;
	//@ spec_public
    private final Suit aSuit;

	//@ requires pRank != null;
	//@ requires pSuit != null;
	//@ ensures this.aRank == pRank;
	//@ ensures this.aSuit == pSuit;
    private Card(Rank pRank, Suit pSuit) {
        aRank = pRank;
        aSuit = pSuit;
    }

	//@ requires pRank != null;
	//@ requires pSuit != null;
	//@ ensures \result != null;
	//@ pure
    public static Card get(Rank pRank, Suit pSuit) {
		//@ show pSuit.ordinal(), pRank.ordinal();
        return CARDS.get(pSuit.ordinal()).get(pRank.ordinal());
    }
	
	/**
	 * Get a flyweight card object based on its serialized form.
	 * 
	 * @param pId The id string for the card. This is needs to have
	 *     been produced by Card.getIDString to be considered a
	 *     valid input to this method.
	 * @return The card object with id string pId
	 */

	//@ requires pId != null;
	//@ requires pId == getIDString();
	public Card get( String pId )
	{
		assert pId != null;
		int id = Integer.parseInt(pId);
		//@ assert (id % Rank.values().length) < Rank.values().length;
		//@ assert (id / Rank.values().length) < Suit.values().length;
		return get(Rank.values()[id % Rank.values().length],
				Suit.values()[id / Rank.values().length]);
	}
	
	/**
	 * Obtain the rank of the card.
	 * @return An object representing the rank of the card.
	 */

	//@ ensures \result == this.aRank;
	//@ pure
	public Rank getRank()
	{
		return aRank;
	}
	
	/**
	 * Return the id string for this card.
	 * 
	 * @return A string uniquely representing this card. The string
	 *     format is not specified except that it is fully compatible
	 *     with the format expected by Card.get(String).
	 */

	//@ ensures \result == Integer.toString(getSuit().ordinal() * Rank.values().length + getRank().ordinal());
	//@ ensures Integer.parseInt(\result) >= 0;
	//@ pure
	public String getIDString()
	{
		return Integer.toString(getSuit().ordinal() * Rank.values().length + getRank().ordinal());
	}
	
	/**
	 * Obtain the suit of the card.
	 * @return An object representing the suit of the card 
	 */

	//@ ensures \result == aSuit;
	//@ pure
	public Suit getSuit()
	{
		return aSuit;
	}
	
	/**
	 * @see java.lang.Object#toString()
	 */

	@Override
	//@ pure
	public String toString()
	{
		String result = aRank + " of " + aSuit;
		return result;
	}
}

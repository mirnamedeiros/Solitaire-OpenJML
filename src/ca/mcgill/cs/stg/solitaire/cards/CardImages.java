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


import java.util.HashMap;
import java.util.Map;

import javafx.scene.image.Image;

/**
 * A class to store and manage images of the 52 cards.
 */
public final class CardImages 
{
	//@ public invariant aCards != null;
	//@ spec_public
	private static final String IMAGE_LOCATION = "";
	//@ spec_public
	private static final String IMAGE_SUFFIX = ".gif";
	//@ spec_public
	private static final String[] RANK_CODES = {"a", "2", "3", "4", "5", "6", "7", "8", "9", "t", "j", "q", "k"};
	//@ spec_public
	private static final String[] SUIT_CODES = {"c", "d", "h", "s"};	
	
	//@ spec_public
	private static Map<String, Image> aCards = new HashMap<String, Image>();
	
	private CardImages()
	{}
	
	/**
	 * Return the image of a card.
	 * @param pCard the target card
	 * @return An icon representing the chosen card.
	 */
	//@ requires pCard != null;
	//@ ensures \result != null;
	public static Image getCard( Card pCard )
	{
		assert pCard != null;
		return getCard( getCode( pCard ) );
	}
	
	//@ requires pCode != null;
	//@ ensures \result == aCards.get( pCode );
	private static Image getCard( String pCode )
	{
		//@ nullable
		Image image = (Image) aCards.get( pCode );
		if( image == null )
		{
			image = new Image(CardImages.class.getClassLoader().getResourceAsStream( IMAGE_LOCATION + pCode + IMAGE_SUFFIX ));
			aCards.put( pCode, image );
		}
		return image;
	}
	
	/**
	 * Return an image of the back of a card.
	 * @return An icon representing the back of a card.
	 */

	//@ ensures \result != null;
	public static Image getBack()
	{
		return getCard( "b" );
	}
	
	//@ requires pCard != null;
	//@ ensures \result != null;
	//@ pure
	public static String getCode( Card pCard )
	{
		return RANK_CODES[ pCard.getRank().ordinal() ] + SUIT_CODES[ pCard.getSuit().ordinal() ];		
	}
}

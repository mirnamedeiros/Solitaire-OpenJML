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
package ca.mcgill.cs.stg.solitaire.gui;

import ca.mcgill.cs.stg.solitaire.cards.Card;
import javafx.event.EventHandler;
import javafx.scene.image.ImageView;
import javafx.scene.input.ClipboardContent;
import javafx.scene.input.Dragboard;
import javafx.scene.input.MouseEvent;
import javafx.scene.input.TransferMode;

/**
 * Stores a string representing the card dragged.
 */
public class CardDragHandler implements EventHandler<MouseEvent>
{
	/*@ spec_public*/private static final ClipboardContent CLIPBOARD_CONTENT = new ClipboardContent();
	
	//@ public invariant aImageView != null;
    //@ public invariant aCard != null;
	/*@ spec_public*/private Card aCard;
	/*@ spec_public*/private ImageView aImageView;
	
	// Variáveis auxiliares para as anotações jml
	public String aCardIdString;
	public String cliboardContentIdString;
	
	//@ requires pView != null;
	//@ ensures aImageView == pView;
	CardDragHandler( ImageView pView )
	{
		aImageView = pView;
	}
	
	// @ requires pCard != null;
	// @ ensures aCard == pCard;
	void setCard(Card pCard)
	{
		aCard = pCard;
	}
	
	//@ also
	// @ requires pMouseEvent != null;
	// @ ensures aCardIdString.equals(cliboardContentIdString);
	// @ ensures cliboardContentIdString == null;
	//@ requires TransferMode.ANY != null;
	@Override
	public void handle(MouseEvent pMouseEvent)
	{
		Dragboard db = aImageView.startDragAndDrop(TransferMode.ANY);
        CLIPBOARD_CONTENT.putString(aCard.getIDString());
        aCardIdString = aCard.getIDString();
        cliboardContentIdString = CLIPBOARD_CONTENT.getString();
        db.setContent(CLIPBOARD_CONTENT);
        pMouseEvent.consume();
	}
}
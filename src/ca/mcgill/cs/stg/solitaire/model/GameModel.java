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
package ca.mcgill.cs.stg.solitaire.model;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import ca.mcgill.cs.stg.solitaire.ai.PlayingStrategy;
import ca.mcgill.cs.stg.solitaire.cards.Card;
import ca.mcgill.cs.stg.solitaire.cards.CardStack;
import ca.mcgill.cs.stg.solitaire.cards.Deck;
import ca.mcgill.cs.stg.solitaire.cards.Rank;
import ca.mcgill.cs.stg.solitaire.cards.Suit;

/**
 * Keeps track of the current state of the game and provides
 * a facade to it. 
 * 
 * The game state can logically be separated into four distinct 
 * conceptual elements: the deck, the discard pile, the foundations
 * where completed suits are accumulated, and the tableau, which consists of
 * seven piles where cards fan down in sequences of alternating suit colors.
 */
public final class GameModel implements GameModelView
{
	// Variáveis para auxiliar em anotações com verificações em testes não puros
	public boolean emptyADiscard = false;
	public boolean emptyATableau = false;
	public boolean emptyAFoundation = false;
	public int aFoundationsSize;
	public boolean aFoundationsPeek;
	public int aDiscardSize;
	public Card aDiscardPeek;
	public boolean aTableauContains = false;
	public int aTableauSize;

	public boolean tableauContainsCard = false;
	public boolean foundationsContainsCard = false;
	public boolean discardContainsCard = false;
	public boolean canMoveFoundation = false;
	public boolean canMoveTableau = false;
	public Location findResult;
	
	private static final Move NULL_MOVE = new Move()
	{
		@Override
		public void perform()
		{} // Does nothing on purpose

		@Override
		public boolean isNull()
		{ return true; }

		@Override
		public void undo()
		{} // Does nothing on purpose
	};
	
	private final Move aDiscardMove = new Move()
	{
		@Override
		public void perform()
		{
			assert !isDeckEmpty();	
			aDiscard.push(aDeck.draw());
			aMoves.push(this);
			notifyListeners();
		}

		@Override
		public void undo()
		{
			assert !isDiscardPileEmpty();
			aDeck.push(aDiscard.pop());
			notifyListeners();
		}
	};
	
	private final Deck aDeck = new Deck();
	/*@ spec_public*/private final Stack<Move> aMoves = new Stack<>();
	/*@ spec_public*/private final CardStack aDiscard = new CardStack();
	private final Foundations aFoundations = new Foundations();
	private final Tableau aTableau = new Tableau();
	private final List<GameModelListener> aListeners = new ArrayList<>();
	private final PlayingStrategy aPlayingStrategy;
	
	/**
	 * Creates a new game model initialized to a new game.
	 * @param pPlayingStrategy The strategy to use for auto-play. 
	 * @pre pPlayingStrategy != null
	 */
	//@ requires pPlayingStrategy != null;
	public GameModel(PlayingStrategy pPlayingStrategy)
	{
		assert pPlayingStrategy != null;
		aPlayingStrategy = pPlayingStrategy;
		reset();
	}
	
	/**
	 * @return The number of cards in the foundations.
	 */
	//@ ensures \result >= 0;
	public int getScore()
	{
		return aFoundations.getTotalSize();
	}
	
	/**
	 * Try to automatically make a move. This may result in nothing happening
	 * if the auto-play strategy cannot make a decision.
	 * @return Whether a move was performed or not.
	 */
	public boolean tryToAutoPlay()
	{
		Move move = aPlayingStrategy.getLegalMove(this);
		move.perform();
		return !move.isNull();
	}
	
	/**
	 * Registers an observer for the state of the game model.
	 * @param pListener A listener to register.
	 * @pre pListener != null
	 */
	
	//@ requires pListener != null;
	public void addListener(GameModelListener pListener)
	{
		assert pListener != null;
		aListeners.add(pListener);
	}
	
	private void notifyListeners()
	{
		//@ assert aListeners != null;
		for( GameModelListener listener : aListeners )
		{
			listener.gameStateChanged();
		}
	}
	
	/**
	 * Restores the model to the state corresponding to the start of a new game.
	 */
	public void reset()
	{
		aMoves.clear();
		aDeck.shuffle();
		aDiscard.clear();
		emptyADiscard = aDiscard.isEmpty();
		aFoundations.initialize();
		aTableau.initialize(aDeck);
		notifyListeners();
	}
	
	/**
	 * @return True if the game is completed.
	 */
	//@ requires Rank.values() != null && Suit.values() != null;
	//@ ensures \result == (aFoundationsSize == Rank.values().length * Suit.values().length);
	public boolean isCompleted()
	{
		aFoundationsSize = aFoundations.getTotalSize();
		return aFoundations.getTotalSize() == Rank.values().length * Suit.values().length;
	}
	
	@Override
	public boolean isDeckEmpty()
	{
		return aDeck.isEmpty();
	}
	
	@Override
	public boolean isDiscardPileEmpty()
	{
		return aDiscard.isEmpty();
	}
	
	@Override
	public boolean isFoundationPileEmpty(FoundationPile pPile)
	{
		return aFoundations.isEmpty(pPile);
	}
	
	/**
	 * Obtain the card on top of the foundation pile pPile
	 * without removing it.
	 * @param pPile The pile to check.
	 * @return The card on top of the pile.
	 * @pre pPile != null && !isFoundationPileEmpty(pIndex)
	 */
	//@ requires pPile != null && emptyAFoundation;
	public Card peekSuitStack(FoundationPile pPile)
	{
		emptyAFoundation = !isFoundationPileEmpty(pPile);
		assert pPile != null && !isFoundationPileEmpty(pPile);
		return aFoundations.peek(pPile);
	}
	
	@Override
	public Card peekDiscardPile()
	{
		assert aDiscard.size() != 0;
		return aDiscard.peek();
	}
	
	/**
	 * @param pCard A card to locate
	 * @return The game location where this card currently is.
	 * @pre the card is in a location where it can be found and moved.
	 */
	//@ requires pCard != null;
	//@ ensures \result != null;
	/*@ ensures (\result == OtherLocation.DISCARD_PILE && emptyADiscard && aDiscardPeek == pCard)
	  	|| (\result != null && \result instanceof FoundationPile && emptyAFoundation && aFoundationsPeek)
		|| (\result != null && \result instanceof TableauPile && aTableauContains);
	*/
	private Location find(Card pCard)
	{
		if( !aDiscard.isEmpty() && aDiscard.peek() == pCard )
		{
			emptyADiscard = true;
			aDiscardPeek = aDiscard.peek();
			return OtherLocation.DISCARD_PILE;
		}
		//@ assert FoundationPile.values() != null;
		for( FoundationPile index : FoundationPile.values() )
		{
			if( !aFoundations.isEmpty(index) && aFoundations.peek(index) == pCard )
			{
				emptyAFoundation = true;
				aFoundationsPeek = true;
				return index;
			}
		}
		//@ assert TableauPile.values() != null;
		for( TableauPile index : TableauPile.values() )
		{
			if( aTableau.contains(pCard, index))
			{
				aTableauContains = true;
				return index;
			}
		}
		assert false; // We did not find the card: the precondition was not met.
		return null;
	}
	
	/**
	 * Undoes the last move.
	 */
	public void undoLast()
	{
		if( !aMoves.isEmpty() )
		{
			aMoves.pop().undo();
		}
	}
	
	/**
	 * @return If there is a move to undo.
	 */
	public boolean canUndo()
	{
		return !aMoves.isEmpty();
	}
	
	/*
	 * Removes the moveable card from pLocation.
	 */
	//@ requires pLocation != null;
	/*@ requires (pLocation == OtherLocation.DISCARD_PILE)
		|| (pLocation instanceof FoundationPile)
		|| (pLocation instanceof TableauPile );
	*/
	//@modifies aDiscard, aFoundations, aTableau;
	/* @ensures !aDiscard.isEmpty() ==> aDiscardSize == \old(aDiscardSize) - 1;
		@ensures pLocation instanceof TableauPile 
			==> aTableauSize == \old(aTableauSize) - 1;
	*/
	private void absorbCard(Location pLocation)
	{
		if( pLocation == OtherLocation.DISCARD_PILE )
		{
			assert !aDiscard.isEmpty();
			aDiscard.pop();
		}
		else if( pLocation instanceof FoundationPile )
		{
			assert !aFoundations.isEmpty((FoundationPile)pLocation);
			aFoundations.pop((FoundationPile)pLocation);
		}
		else
		{
			assert pLocation instanceof TableauPile;
			aTableau.pop((TableauPile)pLocation);
		}
		
		aDiscardSize = aDiscard.size();
		aTableauSize = aTableau.aPilesSize();
	}
	
	//@ requires pCard != null && pDestination != null;
	/*@ requires (pDestination instanceof TableauPile)
		|| (pDestination instanceof FoundationPile) 
		|| (pDestination == OtherLocation.DISCARD_PILE);
	*/
	//@ modifies aTableau, aFoundations, aDiscard;
	/*@ ensures (pDestination instanceof TableauPile) 
		  	==> aTableauContains && aTableauSize == \old(aTableauSize);
		@ ensures (pDestination instanceof FoundationPile) 
	      	==> aFoundationsSize == \old(aFoundationsSize) + 1;
	   	@ ensures (pDestination == OtherLocation.DISCARD_PILE) 
	      	==> aDiscardSize == \old(aDiscardSize) + 1;
	*/
	private void move(Card pCard, Location pDestination)
	{
		Location source = find(pCard);
		if( source instanceof TableauPile && pDestination instanceof TableauPile )
		{
			aTableau.moveWithin(pCard, (TableauPile)source, (TableauPile) pDestination);
		}
		else
		{
			absorbCard(source);
			if( pDestination instanceof FoundationPile )
			{
				aFoundations.push(pCard, (FoundationPile)pDestination);
			}
			else if( pDestination == OtherLocation.DISCARD_PILE )
			{
				aDiscard.push(pCard);
			}
			else
			{
				assert pDestination instanceof TableauPile;
				aTableau.push(pCard, (TableauPile)pDestination);
				aTableauSize = aTableau.aPilesSize();
				aTableauContains = true;
			}
		}
		
		aDiscardSize = aDiscard.size();
		aFoundationsSize = aFoundations.getTotalSize();
	    
		notifyListeners();
	}
	
	@Override
	public CardStack getTableauPile(TableauPile pIndex)
	{
		return aTableau.getPile(pIndex); 
	}
	
	@Override
	public boolean isVisibleInTableau(Card pCard)
	{
		return aTableau.contains(pCard) && aTableau.isVisible(pCard);
	}
	
	@Override
	public boolean isLowestVisibleInTableau(Card pCard)
	{
		return aTableau.contains(pCard) && aTableau.isLowestVisible(pCard);
	}
	
	/**
	 * Get the sequence consisting of pCard and all 
	 * the other cards below it, from the tableau.
	 * @param pCard The top card of the sequence
	 * @param pPile The requested pile
	 * @return A non-empty sequence of cards.
	 * @pre pCard != null and is in pile pPile
	 */
	//@ requires pCard != null && pPile != null;
	//@ ensures \result != null;
	public CardStack getSubStack(Card pCard, TableauPile pPile)
	{
		assert pCard != null && pPile != null && find(pCard) == pPile;
		return aTableau.getSequence(pCard, pPile);
	}

	
	/*@ also
		@ ensures \result ==> (pDestination instanceof FoundationPile && canMoveFoundation)
		|| (pDestination instanceof TableauPile && canMoveTableau)
		|| (!\result);
	*/
	@Override
	public boolean isLegalMove(Card pCard, Location pDestination )
	{ 
		if( pDestination instanceof FoundationPile )
		{
			canMoveFoundation = true;
			return aFoundations.canMoveTo(pCard, (FoundationPile) pDestination);
		}
		else if( pDestination instanceof TableauPile )
		{
			canMoveTableau = true;
			return aTableau.canMoveTo(pCard, (TableauPile) pDestination);
		}
		else
		{
			return false;
		}
	}
	
	@Override
	public Move getNullMove()
	{
		return NULL_MOVE;
	}
	
	@Override
	public Move getDiscardMove()
	{
		return aDiscardMove;
	}
	
	@Override
	public Move getCardMove(Card pCard, Location pDestination)
	{
		Location source = find( pCard );
		if( source instanceof TableauPile  && aTableau.revealsTop(pCard))
		{
			return new CompositeMove(new CardMove(pCard, pDestination), new RevealTopMove((TableauPile)source) );
		}
		return new CardMove(pCard, pDestination);
	} 
	
	@Override
	public boolean isBottomKing(Card pCard)
	{
		assert pCard != null && aTableau.contains(pCard);
		return aTableau.isBottomKing(pCard);
	}

	
	/**
	 * A move that represents the intention to move pCard
	 * to pDestination, possibly including all cards stacked
	 * on top of pCard if pCard is in a working stack.
	 */
	private class CardMove implements Move
	{
		private Card aCard;
		private Location aOrigin; 
		private Location aDestination; 
		
		//@ requires pCard != null && pDestination != null;
		CardMove(Card pCard, Location pDestination)
		{
			aCard = pCard;
			aDestination = pDestination;
			aOrigin = find(pCard);
		}

		//@ also 
		//@ ensures aMoves.size() == \old(aMoves.size()) + 1;
		@Override
		public void perform()
		{
			assert isLegalMove(aCard, aDestination);
			move(aCard, aDestination);
			aMoves.push(this);
		}

		@Override
		public void undo()
		{
			move(aCard, aOrigin);
		}
	}
	
	/**
	 * reveals the top of the stack.
	 *
	 */
	private class RevealTopMove implements Move
	{
		private final TableauPile aIndex;
		
		//@ requires pIndex != null;
		RevealTopMove(TableauPile pIndex)
		{
			aIndex = pIndex;
		}
		
		//@ also 
		//@ ensures aMoves.size() == \old(aMoves.size()) + 1;
		@Override
		public void perform()
		{
			aTableau.showTop(aIndex);
			aMoves.push(this);
			notifyListeners();
		}

		//@ also 
		//@ ensures aMoves.size() == \old(aMoves.size()) - 1;
		@Override
		public void undo()
		{
			aTableau.hideTop(aIndex);
			aMoves.pop().undo();
			notifyListeners();
		}
	}
}

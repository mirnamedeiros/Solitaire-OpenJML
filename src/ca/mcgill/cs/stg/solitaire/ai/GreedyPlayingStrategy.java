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
package ca.mcgill.cs.stg.solitaire.ai;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import ca.mcgill.cs.stg.solitaire.cards.Card;
import ca.mcgill.cs.stg.solitaire.cards.CardStack;
import ca.mcgill.cs.stg.solitaire.model.FoundationPile;
import ca.mcgill.cs.stg.solitaire.model.GameModelView;
import ca.mcgill.cs.stg.solitaire.model.Move;
import ca.mcgill.cs.stg.solitaire.model.TableauPile;

/**
 * Makes the first possible move in this order: 
 * 1. Discarding if the discard pile is empty;
 * 2. Moving a card from the discard pile to a foundation pile;
 * 3. Moving a card from the discard pile to the tableau;
 * 4. Moving a card from the tableau to a foundation pile, in order
 * of piles;
 * 5. Moving from one pile in the tableau to another, if this either reveals
 * a fresh card or frees up a pile for a king.
 * 6. None of the above was possible, discards if possible.
 * 7. If discarding was not possible, return the null move.
 */
public class GreedyPlayingStrategy implements PlayingStrategy
{
	//@ spec_public
	private static final List<Function<GameModelView, Move>> SUBSTRATEGIES = new ArrayList<>();

	//@ ensures SUBSTRATEGIES.size() == 6;
	static
	{
		SUBSTRATEGIES.add(GreedyPlayingStrategy::substrategyDiscardIfDiscardPileIsEmpty);
		SUBSTRATEGIES.add(GreedyPlayingStrategy::substrategyMoveDiscardToFoundation);
		SUBSTRATEGIES.add(GreedyPlayingStrategy::substrategyMoveDiscardToTableau);
		SUBSTRATEGIES.add(GreedyPlayingStrategy::substrategyMoveFromTableauToFoundation);
		SUBSTRATEGIES.add(GreedyPlayingStrategy::substrategyMoveWithinTableau);
		SUBSTRATEGIES.add(GreedyPlayingStrategy::substrategyDiscard);
	}
	
	/*
	 * Variáveis para auxiliar nas anotações JML 
	 */
	/*@spec_public*/ static boolean checkIsEmpty;
	/*@spec_public*/ static Move nullMove;
	/*@spec_public*/ static Move cardMove;
	/*@spec_public*/ static boolean isBottomKing = false;
	/*@spec_public*/ static boolean isLowestVisibleInTableau = false;
	/*@spec_public*/ static boolean isLegalMove = false;
	
	/**
	 * Creates a new strategy.
	 */
	public GreedyPlayingStrategy() {}
	
	/*
	 * If the discard pile is empty, discard. 
	 */
	//@ requires pModel != null;
	//@ ensures \result != null;
	private static Move substrategyDiscardIfDiscardPileIsEmpty(GameModelView pModel)
	{
		if( pModel.isDiscardPileEmpty() && !pModel.isDeckEmpty() )
		{
			return pModel.getDiscardMove();
		}
		else
		{
			return pModel.getNullMove();
		}
	}
	
	/*
	 * If it's possible to move the top of the discard pile to the foundation, do it.
	 */
	//@ requires pModel != null;
	//@ requires !checkIsEmpty;
	//@ ensures \result != null;
	private static Move substrategyMoveDiscardToFoundation(GameModelView pModel)
	{
		checkIsEmpty = pModel.isDeckEmpty();
		
		if( pModel.isDiscardPileEmpty() )
		{
			return pModel.getNullMove();
		}
		
		//@ assert FoundationPile.values() != null;
		//@ loop_invariant pile == FoundationPile.FIRST || pile == FoundationPile.SECOND || pile == FoundationPile.THIRD || pile == FoundationPile.FOURTH;
		//@ loop_modifies \nothing;
		for(FoundationPile pile : FoundationPile.values())
		{
			
			if( pModel.isLegalMove(pModel.peekDiscardPile(), pile))
			{
				return pModel.getCardMove(pModel.peekDiscardPile(), pile);
			}
		}
		return pModel.getNullMove();
	}
	
	//@ requires pModel != null;
	//@ ensures \result != null;
	private static Move substrategyMoveDiscardToTableau(GameModelView pModel)
	{
		if( pModel.isDiscardPileEmpty() )
		{
			return pModel.getNullMove();
		}
		
		//@ assert TableauPile.values() != null;
		//@ loop_invariant pile == TableauPile.FIRST || pile == TableauPile.SECOND || pile == TableauPile.THIRD || pile == TableauPile.FOURTH || pile == TableauPile.FIFTH || pile == TableauPile.SIXTH || pile == TableauPile.SEVENTH;
		//@ loop_modifies \nothing;
		for(TableauPile pile : TableauPile.values())
		{
			if( pModel.isLegalMove(pModel.peekDiscardPile(), pile))
			{
				return pModel.getCardMove(pModel.peekDiscardPile(), pile);
			}
		}
		return pModel.getNullMove();
	}
	
	//@ requires pModel != null;
	//@ ensures \result != null;
	private static Move substrategyMoveFromTableauToFoundation(GameModelView pModel)
	{
		//@ assert TableauPile.values() != null;
		for(TableauPile tableauPile : TableauPile.values())
		{
			CardStack stack = pModel.getTableauPile(tableauPile);
			if( !stack.isEmpty() )
			{
				Card card = stack.peek();
				
				//@ assert FoundationPile.values() != null;
				//@ loop_invariant foundationPile == FoundationPile.FIRST || foundationPile == FoundationPile.SECOND || foundationPile == FoundationPile.THIRD || foundationPile == FoundationPile.FOURTH;
				//@ loop_modifies \nothing;
				for(FoundationPile foundationPile : FoundationPile.values())
				{
					if( pModel.isLegalMove(card, foundationPile))
					{
						return pModel.getCardMove(card, foundationPile);
					}
				}
			}	
		}
		return pModel.getNullMove();
	}
	
	/* Only if it reveals a card or empties a pile. We also don't move kings between empty piles */
	//@ requires pModel != null;
	/*@ ensures (\result == nullMove) 
		|| (isBottomKing == false && isLowestVisibleInTableau == true && isLegalMove == true && \result == cardMove)
		|| (isBottomKing == false && isLowestVisibleInTableau == true && isLegalMove == false && \result == nullMove)
		|| (isBottomKing == false && isLowestVisibleInTableau == false && isLegalMove == false && \result == nullMove)
		|| (isBottomKing == true && isLowestVisibleInTableau == false && isLegalMove == false && \result == nullMove);
	*/ 
	//@ ensures \result != null;
	private static Move substrategyMoveWithinTableau(GameModelView pModel)
	{
		nullMove = pModel.getNullMove();
		
		//@ assert TableauPile.values() != null;
		for( TableauPile pile : TableauPile.values())
		{
			CardStack stack = pModel.getTableauPile(pile);
			
			//@ assert stack != null;
			for( Card card : stack )
			{
				if( pModel.isBottomKing(card))
				{
					isBottomKing = true;
					continue;
				}
				
				if( pModel.isLowestVisibleInTableau(card))
				{
					isLowestVisibleInTableau = true;
					
					//@ assert TableauPile.values() != null;
					for( TableauPile pile2 : TableauPile.values() )
					{
						if( pModel.isLegalMove(card, pile2))
						{
							isLegalMove = true;
							cardMove = pModel.getCardMove(card, pile2);
							return pModel.getCardMove(card, pile2);
						}
					}
				}
			}
		}
		return pModel.getNullMove();
	}
	
	//@ requires pModel != null;
	//@ ensures \result != null;
	private static Move substrategyDiscard(GameModelView pModel)
	{
		if( pModel.isDeckEmpty() )
		{
			return pModel.getNullMove();
		}
		else
		{
			return pModel.getDiscardMove();
		}
	}
	
	@Override
	public Move getLegalMove(GameModelView pModel)
	{
		//@ loop_invariant (\forall int i; 0 <= i && i < SUBSTRATEGIES.size());
		for( Function<GameModelView, Move> substrategy : SUBSTRATEGIES )
		{
			Move move = substrategy.apply(pModel);
			if( !move.isNull() )
			{
				return move;
			}
		}
		return pModel.getNullMove();
	}
}

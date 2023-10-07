open Project_Sigs
open invariants

pred addPhoto[s1, s2: Nicebook, u1: User, p: Photo] {
	//Pre-condition:
	
	// The photo `p` should not be owned by anyone in the initial state (s1)
	p not in s1.users.owns

	// The photo `p` should not be on any wall in the initial state (s1)
	p not in s1.users.has.contains
	// The photo `p` should not be on any wall in the next state (s2)
	p not in s2.users.has.contains	
	// nothing should be attached to new photo
    #(^attachedTo.p) = 0
	//true
	//Post-condition:
	
	// A user's (u1) state is updated to reflect that they now own the photo `p`
	some u2: User {
		// In the updated user state `u2`, the photo `p` is added to their owned content
		u2.owns = u1.owns + p
		
		// The friend list of the user remains unchanged between the old state `u1` and new state `u2`
		u2.friends = u1.friends
		
		// The wall that the user is associated with remains unchanged between the old state `u1` and new state `u2`
		u2.has = u1.has
		
		// The system state `s2` reflects the updated user state `u2` and excludes the old user state `u1`
		s2.users = s1.users + u2 - u1
		
		// The ownership of photos in the system state `s2` is updated to include the photo `p`
		s2.users.owns = s1.users.owns + p
		s2.users.has = s1.users.has	

		//Ensure the privacy of the new user is the same as the old ones
		u2.sharePrivacy = u1.sharePrivacy
		u2.viewPrivacy	= u1.viewPrivacy						
	}
}


pred removePhoto[s1, s2: Nicebook, u1, u2: User, p: Photo, w1, w2: Wall] {
	//Pre-condition:
	
	// The user `u1` should be the owner of the photo `p` in the initial state (s1)
	p in u1.owns
	
	// The walls `w1` and `w2` must be distinct entities
	w1 != w2
	
	//Post-condition:
	
	// The new user state `u2` should reflect that the photo `p` and any content attached to `p` are no longer owned by the user
	u2.owns = u1.owns - p - ^attachedTo.p 
	
	// The friends list remains unchanged between the old and new user state
	u2.friends = u1.friends 
	
	// Define the relationship between the user and their wall
	// In the initial state (s1), user `u1` is related to wall `w1`
	u1.has = w1
	// In the updated state (s2), user `u2` is related to wall `w2`
	u2.has = w2
	
	// On the new wall `w2`, the photo `p` and all content attached to `p` are removed
	w2.contains = w1.contains - p - ^attachedTo.p 

	// Ensure that the content attached to the photo `p` doesn't appear on the new wall `w2`
	^attachedTo.p not in w2.contains
	
	// The system state `s2` should reflect the updated user state `u2` and exclude the old user state `u1`
	s2.users = s1.users + u2 - u1

	// For any user `u3` that owns content attached to the photo `p`, their state should also be updated to reflect the removal of the attached content
	all u3: owns.(^attachedTo.p) - u1 | removeCommentIfAttachTo[s1,s2, u3, p]
	//Ensure the privacy of the new user is the same as the old ones
	u2.sharePrivacy = u1.sharePrivacy
	u2.viewPrivacy	= u1.viewPrivacy
}



pred removeCommentIfAttachTo[s1, s2: Nicebook, u3: User, c: Content]{
	//Pre-condition:
	
	// The user `u3` should be present in the initial state (s1)
	u3 in s1.users
	
	// The content `c`, which could be a comment or photo, should be present in the system in the initial state (s1)
	c in s1.users.owns

	//Post-condition:
	
	// We'll define a new user state `u4` that represents the user after the content removal process
	some u4: User {
			
		// In the updated user state, the ownership set should exclude the content `c` and any content attached to `c`
		u4.owns = u3.owns - ^attachedTo.c
		
		// The wall state remains unchanged (i.e., whatever was on the user's wall remains the same)
		u4.has = u3.has
		
		// The new system state `s2` will now reflect the updated user state `u4` and exclude the old user state `u3`
		s2.users = s1.users - u3 + u4
	
		//Ensure the privacy of the new user is the same as the old ones
		u4.sharePrivacy = u3.sharePrivacy
		u4.viewPrivacy	= u3.viewPrivacy
	}
}


pred publish[s1, s2: Nicebook, u1: User, p: Photo] {
	//Pre-condition:
	
	// The photo must be owned by the user (u1) in the initial state (s1)
	p in u1.owns
	
	// The photo should not be already published (i.e., it shouldn't be on the user's wall already)
	p not in u1.has.contains

	//Post-condition:
	
	// We'll be defining a new user state (u2) for the updated status after publishing the photo
	some u2: User {
			
		// This new user state (u2) should be distinct from the initial user state (u1)
		u2 != u1
		
		// We need to create an updated wall state (w2) for u2 to reflect the newly published photo
		some w2: Wall {
			
			// This updated wall (w2) shouldn't be the same as the initial user's wall
			w2 not in u1.has
			
			// The new wall state (w2) should include the photo in addition to the contents of the initial wall
			w2.contains = u1.has.contains + p 
			
			// Linking the new user state (u2) with the new wall state (w2)
			u2.has = w2
			has.w2 = u2
		}
		
		// The new user state (u2) retains the set of photos owned by the user from the initial state (i.e., the frame condition for the owned content remains unchanged)
		u2.owns = u1.owns
		
		// Similarly, the new user state (u2) retains the friendship relations from the initial user state (u1)
		u2.friends = u1.friends 
		//Ensure the privacy of the new user is the same as the old ones
		u2.sharePrivacy = u1.sharePrivacy
		u2.viewPrivacy	= u1.viewPrivacy
		
		// Finally, the new system state (s2) should reflect the updated user state (u2) without the old user state (u1)
		s2.users = s1.users + u2 - u1
	}
}


pred addCommentForSelf[s1, s2: Nicebook, c1:Content ,c: Comment, u1,u3:User] {
	//Pre-condition:
	
	// Both the content owner (u1) and the commenter (u3) should be present in the old state
	u1 in s1.users
	u3 in s1.users
	
	// Confirming that the content owner and the commenter are indeed the same user
	u1 = u3
	
	// The piece of content should be owned by the owner
	c1 in u1.owns
	
	// The comment shouldn't exist in the initial state
	c not in s1.users.owns
	
	// The comment and the content it's attached to should be distinct entities
	c != c1

	// Ensuring that the comment isn't linked to itself or to other comments in a cyclic manner
	(c not in c.^attachedTo) and (c not in ^attachedTo.c)
	
	// The content (c1) should be a part of the content owned by users in the initial state
	c1 in s1.users.owns
	
	// Similar check to ensure non-cyclic nature of comments
	(c not in c.^attachedTo) and (c not in ^attachedTo.c)
	
	//Post-condition:
	
	// The comment should be associated with only the intended content
	c.attachedTo = c1
	#c.attachedTo = 1

	// Update the user's state to reflect the new comment
	some u2: User, w2: Wall {
		// The new wall state should incorporate the new comment
		w2.contains = (u1.has).contains+c
		// The new comment should only be present on this updated wall
		contains.c = w2
		// The new user state should now own the comment
		u2.owns = u1.owns + c
		u2.has = w2
		has.w2 = u2
		// Retaining the friendship relations from the old state for the new user state
		u2.friends = u1.friends

		// Retaining the privacy from the old state for the new user state
		u2.sharePrivacy = u1.sharePrivacy
		u2.viewPrivacy	= u1.viewPrivacy
	

		// The new state of the system should reflect the updated user without the old user
		s2.users = s1.users - u1 + u2
	}
}


pred addCommentForDifferentUser[s1, s2: Nicebook, c1:Content ,c: Comment, u1,u3:User] {
	// Pre-condition:
	// The user (u1) who owns the content is present in the old state.
	u1 in s1.users
	
	// The user (u3) who will comment is present in the old state.
	u3 in s1.users
	
	// The content to be commented on is owned by u1.
	c1 in u1.owns
	
	// The comment should not already exist in the old state.
	c not in s1.users.owns
	
	// The comment shouldn't be already owned by the commenting user (u3).
	c not in u3.owns 
	
	// Ensure the comment and the content are distinct.
	c != c1

	// Check cyclic conditions to ensure comment is not cyclically attached.
	(c not in c.^attachedTo) and (c not in ^attachedTo.c)
	c1 in s1.users.owns
	
	// Verify privacy settings before adding a comment.
	(u3 in (u1).friends and c1.commentPrivacy != OnlyMe and u1.viewPrivacy!=OnlyMe)
	or (u3 in (u1).friends.friends and (u1.viewPrivacy=Everyone or u1.viewPrivacy=FriendsOfFriends)
	and  (c1.commentPrivacy=Everyone  or c1.commentPrivacy=FriendsOfFriends))
	
	// Post-condition:
	// Ensure that the comment is attached to just one content.
	c.attachedTo = c1
	#(c.attachedTo) = 1

	// Update the users and walls to reflect the added comment.
	some u2, u4: User{
			some w2:Wall{
				// Update the commenter's state.
				u4.owns=u3.owns+c
				u4.friends = u3.friends
				u4.has = u3.has
				
				u4.sharePrivacy = u3.sharePrivacy
				u4.viewPrivacy	= u3.viewPrivacy
	
				// Update the content owner's state to include the new comment on their wall.
				w2.contains = (u1.has).contains+c
				//new comment must be only on new wall
				contains.c = w2
				//set new wall
				u2.has = w2
				has.w2 = u2

				// Frame conditions: Ensure other attributes remain consistent.
				u2.friends = u1.friends
				u2.owns = u1.owns

				//Ensure the privacy of the new user is the same as the old ones
				u2.sharePrivacy = u1.sharePrivacy
				u2.viewPrivacy	= u1.viewPrivacy
			}
			//update new state with new users
			s2.users = s1.users - u1 + u2 - u3 + u4
	}
}

pred addComment[s1, s2: Nicebook, c1:Content ,c: Comment, u1,u3:User]{
	// Decision-making based on whether the content owner and the commenter are the same user or different users:
	
	// If the content owner (u1) and the commenter (u3) are the same:
	// Use the predicate that handles comments made by the content owner themselves.
	(u1 = u3)  implies addCommentForSelf[s1,s2,c1,c,u1,u3] 
	
	// Otherwise, if they are different users:
	// Use the predicate that handles comments made by a different user on the content.
	else addCommentForDifferentUser[s1,s2,c1,c,u1,u3]
}

pred share[s1, s2: Nicebook, u1,u2:User,  p:Photo]{
	// Pre-condition:
	// The user (u1) owning the content is present in the old state.
	u1 in s1.users
	
	// The content (photo) to be shared must be owned by u1.
	p in u1.owns
	
	// The user (u2) who will share the content is distinct from the owner (u1).
	u2 != u1
	
	// The sharing permissions should allow u2 to share the content of u1.
	// Check if u2 is a direct friend of u1 and verify the privacy settings.
	(u2 in (u1).friends and (owns.p).sharePrivacy != OnlyMe and (owns.p).viewPrivacy!=OnlyMe)
	// Alternatively, check if u2 is a friend of a friend of u1 and verify the privacy settings.
	or (u2 in (u1).friends.friends and ((owns.p).viewPrivacy=Everyone or (owns.p).viewPrivacy=FriendsOfFriends)
	and  ((owns.p).sharePrivacy=Everyone  or (owns.p).sharePrivacy=FriendsOfFriends))

	// Post-condition:
	// An instance of the shared content should be present on the wall of u2.
	some u3: User{
		some w3:Wall{
			// Ensure the new user state (u3) is distinct from u2.
			u2 != u3
			
			// The new wall state (w3) should be distinct from the walls of both u1 and u2.
			w3 not in u2.has + u1.has
			
			// Add the shared content (photo) to the new wall.
			w3.contains = u2.has.contains + p
			u3.has = w3
			has.w3 = u3
			
			// Frame conditions: Ensure other attributes of u3 remain consistent.
			u3.friends = u2.friends
			u3.owns = u2.owns

			//Ensure the privacy of the new user is the same as the old ones
			u3.sharePrivacy = u2.sharePrivacy
			u3.viewPrivacy	= u2.viewPrivacy
		}
		
		// Update the new state with the new user.
		s2.users = s1.users - u2 + u3
	}
}


pred unpublish[s1, s2: Nicebook, u1, u2: User, c: Content, w1, w2: Wall] {
	// The predicate checks the type of the content to be unpublished.
	// If the content is a Photo, it uses the unpublishPhoto predicate.
	// Otherwise, it uses the unpublishComment predicate.

	// Check if content 'c' is a Photo.
	(c in Photo) 
	// If 'c' is a Photo, unpublish it as a photo.
	implies unpublishPhoto[s1,s2,u1,u2,c,w1,w2] 
	// If 'c' is not a Photo, unpublish it as a comment.
	else unpublishComment[s1,s2,u1,u2,c,w1,w2]
}


pred unpublishPhoto[s1, s2: Nicebook, u1, u2: User, p: Photo, w1, w2: Wall] {
	// Pre-condition:
	// The operation can proceed only if the photo is owned by the user (u1).
	p in u1.owns

	// Safety check to ensure the two walls are distinct.
	w1 != w2
	
	// Post-condition:
	// In the new state (u2), the photo and any content attached to it are no longer owned by the user.
	u2.owns = u1.owns - ^attachedTo.p 

	// Frame condition to maintain friendships.
	u2.friends = u1.friends 
	
	// Updating the relationship between the User and Wall.
	// Ensure that the user (u1) is linked to the old wall (w1) and the new user (u2) to the new wall (w2).
	u1.has = w1
	u2.has = w2
	
	// Remove the photo and all content attached to it from the owner's wall.
	w2.contains = w1.contains - p - ^attachedTo.p 

	// Ensure that the comments attached to the photo are not in the new wall (w2).
	^attachedTo.p not in w2.contains

	//Ensure the privacy of the new user is the same as the old ones
	u2.sharePrivacy = u1.sharePrivacy
	u2.viewPrivacy	= u1.viewPrivacy
	
	// Update the user set in the new state by replacing the old user (u1) with the new user (u2).
	s2.users = s1.users + u2 - u1
	
	

	// Handling removal for other users who had comments attached to the main photo.
	// The operation can proceed for each such user (u3).
	all u3: owns.(^attachedTo.p) - u1 | removeCommentIfAttachTo[s1,s2, u3, p]
}



pred unpublishComment[s1, s2: Nicebook, u1, u2: User, c: Comment, w1, w2: Wall] {
	// Pre-condition:
	// The operation can proceed only if the comment is owned by the user (u1).
	c in u1.owns

	// The operation can proceed only if the comment is not cyclic in the old state (s1).
	commentNotCyclic[s1]

	// The operation can proceed only if the comment is not cyclic in the new state (s2).
	commentNotCyclic[s2]

	// The operation can proceed only if the user (u1) exists in the old state and the user (u2) does not.
	u1 in s1.users
	u2 not in s1.users

	// Safety check to ensure the two walls are distinct.
	w1 != w2
	
	// Post-condition:
	// In the new state (u2), the comment and any content attached to it are no longer owned by the user.
	u2.owns = u1.owns - c - ^attachedTo.c 

	// Frame condition to maintain friendships.
	u2.friends = u1.friends 

	// Updating the relationship between the User and Wall.
	u1.has = w1
	u2.has = w2

	// Remove the comment and all content attached to it from the owner's wall.
	w2.contains = w1.contains - c - ^attachedTo.c 

	// Ensure that the comments attached to the main comment are not in the new wall (w2).
	^attachedTo.c not in w2.contains

	//Ensure the privacy of the new user is the same as the old ones
	u2.sharePrivacy = u1.sharePrivacy
	u2.viewPrivacy	= u1.viewPrivacy
	// Update the user set in the new state by replacing the old user (u1) with the new user (u2).
	s2.users = s1.users + u2 - u1

	// Handling removal for other users who had comments attached to the main comment.
	// The operation can proceed for each such user (u3).
	all u3: owns.(^attachedTo.c) - u1 | removeCommentIfAttachTo[s1,s2, u3,c]
}

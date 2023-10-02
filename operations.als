open Project_Sigs


pred addPhoto[s1, s2: Nicebook, u1: User, p: Photo] {
	//pre condition 
	//true
	//post condition
	//add photo to user owns content
	some u2: User {
		u2.owns = u1.owns + p
		u2.friends = u1. friends 
		u2.has = u1.has
		s2.users = s1.users + u2 -u1
	}
}

pred removePhoto[s1, s2: Nicebook, u1, u2: User, p: Photo, w1, w2: Wall] {
	//pre condition 
	//photo must be owned by user (u1)
	p in u1.owns
	
	// Ensure w1 and w2 are distinct
	w1 != w2
	
	//post condition
	//new user state
	u2.owns = u1.owns - p
	u2.friends = u1.friends 
	
	//Ensure the relationship between User and Wall
	u1.has = w1
	u2.has = w2
	
	//remove photo from owner wall
	w2.contains = w1.contains - p 
	
	s2.users = s1.users + u2 - u1
}


pred publish[s1, s2: Nicebook, u1, u2: User, p: Photo, w1, w2: Wall] {
	//pre condition 
	//photo must be owned by user (u1)
	p in u1.owns
	//photo must not already be on user (u1) wall
	p not in u1.has.contains
	
	// Ensure w1 and w2 are distinct
	w1 != w2
	
	//post condition

	//add photo from owner wall
	w2.contains = w1.contains + p 
	//new user state
	u2.owns = u1.owns
	u2.friends = u1.friends 
	//Ensure the relationship between User and Wall
	u1.has = w1
	u2.has = w2

	//add new user to new state
	s2.users = s1.users + u2 - u1

}
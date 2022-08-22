def localize(v,w):                      #loc(X^v at w)
    if v==s[1]*s[1]: return 1
#   if (w=='l'): w=W.long_element()     #point to localize at.
#   v=prod(s[i] for i in v)             #Schubert variety X^v to be localized 
    lenv=v.length()
    wWord=w.reduced_word()
#    reducedWords=[tuple(x) for x in v.reduced_words()]
    subwords=[]
    for vi in v.reduced_words():
#    for vi in reducedWords:
        outerList=[[] for _ in range(lenv)]
        positionsOf={k:[] for k in range(1,rank+1)}
        for (pos,ref) in enumerate(wWord): positionsOf[ref].append(pos)
        for (index,ref) in enumerate(vi): outerList[index]=positionsOf[ref]
#       def isIncreasing(l): return all(x<y for (x,y) in zip(l[:-1],l[1:]))
#       n=filter(isIncreasing,product(*outerList))
        if outerList:
            n=[[x] for x in outerList[0]]
            for innerList in outerList[1:]:
                n=[ni+[b] for ni in n for b in innerList if ni[-1]<b]
            subwords.extend(n)
    q=0
    for subword in subwords:
        u=s[1]*s[1] #[x for x in W.elements_of_length(0)][0]
        p=1    
        for (oi,i) in zip([0]+subword,subword):
            u=prod((s[wWord[k]] for k in range(oi,i)),z=u)
            p*=to_poly(u.action(alpha[wWord[i]]))
#        for i in subword:
#            if (i!=0): u=u*prod(s[wWord[k]] for k in range(oi,i))
#            p*=to_poly(u.action(alpha[wWord[i]]))
#            oi=i
        q+=p
    return(q)


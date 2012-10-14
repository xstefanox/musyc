#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Copyright (c) 2012, Stefano Varesi
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice, this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY Stefano Varesi ``AS IS'' AND ANY
# EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL <copyright holder> BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


__prog__ = u'musyc'
__author__ = u"Stefano Varesi stefano.varesi@gmail.com"
__description__ = u'Personal music database manager'
__version__ = u'0.9-beta2'


################
# DEPENDENCIES #
################


import musyc
import sys
import argparse
import traceback
import re
import os
import os.path
import pystache
import lxml.etree
import termcolor
import Image
import shutil
import subprocess
import inspect
import tempfile
import mimetypes
import xml.dom.minidom
import lxml.etree
import mutagen


#from xspf import Xspf, Track


#############
# CONSTANTS #
#############


BAD_CHARACTERS = re.compile(r"[ \!\?\|\*\<\>\/\n\r\\:\&]")

BAD_LINE_ENDINGS = re.compile(r"\r(?!\n)|(?<!\r)\n")

# @TODO: unused, remove?
UNIX_NEWLINES = re.compile(r"[^\r]\n")

METADATA_FILE = u"metadata.xml"

COVER_IMAGE = u"folder.jpg"

THUMBNAIL_IMAGE = u"thumb.jpg"

METADATA_XML_TEMPLATE = unicode(open(os.path.join(os.path.dirname(musyc.__file__), METADATA_FILE), 'r').read())

VALID_GENRES = tuple(sorted([ g.replace('\n', '') for g in open(os.path.join(os.path.dirname(musyc.__file__), 'valid_genres.list'), 'r').readlines() if g != '\n' ]))

VALID_MIME_TYPES = tuple(sorted([ g.replace('\n', '') for g in open(os.path.join(os.path.dirname(musyc.__file__), 'valid_mime_types.list'), 'r').readlines() if g != '\n' ]))

ALBUM_XSD = lxml.etree.XMLSchema(lxml.etree.XML(pystache.render(open(os.path.join(os.path.dirname(musyc.__file__), 'album.xsd.mustache'), 'r').read(), { 'genres': [ { 'genre': g } for g in VALID_GENRES ] })))

del g

##################
# UTIL FUNCTIONS #
##################


def sanitize(string):

    '''Remove invalid characters from a string'''

    return BAD_CHARACTERS.sub("_", string)


####################
# OUTPUT FUNCTIONS #
####################


def print_header(msg):

    '''
    Print a list header, in the form:
    >>> <intestazione>
    '''
    
    print(termcolor.colored('>>> ', 'green', attrs = [ 'bold' ]) + msg)


def print_item(msg):

    '''
    Print an element of a list, in the form:
    --> <elemento>
    '''

    print(termcolor.colored('--> ', 'yellow', attrs = [ 'bold' ]) + msg)


####################
# ALBUM MANAGEMENT #
####################


class CommandProcessor:

    def __init__(self, cmdline):
        if len(cmdline) == 1:
            self.command = getattr(self.__class__, "help")
            self.args = None
        else:
            self.command = cmdline[1]
            # se non e' stato fornito un path
            if len(cmdline[2:]) == 0:
                # usa la directory corrente
                self.targetdir = os.getcwd()
            else:
                self.targetdir = cmdline[2]
            # controlla se la directory esiste
            if not os.path.isdir(self.targetdir):
                raise Exception("Il percorso fornito non e' una directory")
            # salva gli altri argomenti
            self.args = cmdline[3:]
            # se il comando inizia con "__", allora non e' valido
            if self.command.startswith("__"):
                raise Exception("Comando non supportato")
            # se il comando non e' un metodo di questa classe,
            # allora non e' valido
            try:
                self.command = getattr(self.__class__, self.command)
            except AttributeError:
                raise Exception("Comando non supportato")
        # converti a Unicode tutte le stringhe:
        # cmd potrebbe essere un metodo, quindi occorre controllare se e' una stringa
        if isinstance(self.command, str):
            self.command = unicode(self.command, "utf-8")
        # targetdir potrebbe non esistere
        if "targetdir" in dir(self):
            self.targetdir = unicode(self.targetdir, "utf-8")
        # args potrebbe essere None
        if self.args:
            self.args =  map(lambda arg: unicode(arg, "utf-8"), self.args)


    def convert(self):

        '''Converte i vecchi file di configurazione nei nuovi'''
        
        raise Exception('Not implemented')
        
        # se il file di configurazione non esiste
        oldconfig = os.path.join(self.targetdir, "metadata.xml")
        
        if not os.path.isfile(oldconfig):
            return
        
        album = Album(self.targetdir)
        
        x = Xspf()
        x.title = album.title
        x.creator = album.author
        x.date = album.year
        
        for idx, f in enumerate(album.audiofiles):
            tr = Track()
            tr.title = album.tracklist[idx]
            x.add_track(tr)
        
        print(xml.dom.minidom.parseString(x.toXml()).toprettyxml())
        
        return
#        # se il file contenente la tracklist non esiste
#        oldtracklist = os.path.join(self.targetdir, "tracklist.txt")
#        if not os.path.isfile(oldtracklist):
#            raise Exception("Il vecchio file contenente la tracklist non esiste")

        ( autore , titolo , anno , genere , split ) = subprocess.Popen("source \"" + oldconfig + "\" && /bin/echo -n \"$AUTORE\n$TITOLO\n$ANNO\n$GENERE\n$SPLIT\n\"", shell = True, stdout = subprocess.PIPE).communicate()[0].splitlines()

        # converti in Unicode
        autore = unicode(autore, "utf-8")
        titolo = unicode(titolo, "utf-8")
        genere = unicode(genere, "utf-8")
        
        # crea il file di configurazione vuoto
        new_config = xml.dom.minidom.parseString(METADATA_XML_TEMPLATE)

        # inserisci il titolo
        title_element = new_config.getElementsByTagName("title")[0]
        title_element.appendChild(new_config.createTextNode(titolo))

        # inserisci l'anno
        new_config.getElementsByTagName("year")[0].appendChild(new_config.createTextNode(anno))

        # inserisci il genere
        new_config.getElementsByTagName("genre")[0].appendChild(new_config.createTextNode(genere))

        author_elements = new_config.getElementsByTagName("author")

        # se l'album e' uno split
        if len(split) != 0:
            # prepara la lista degli autori
            autore = map(lambda x: x.strip(), autore.split("&"))
            # inserisci il secondo autore
            second_author_element = author_elements[0]
            second_author_element.appendChild(new_config.createTextNode(autore[1]))
            space_element = new_config.createTextNode("\n    ")
            new_config.documentElement.insertBefore(space_element, second_author_element)
            # inserisci il primo autore
            first_author_element = new_config.createElement("author")
            first_author_element.appendChild(new_config.createTextNode(autore[0]))
            new_config.documentElement.insertBefore(first_author_element, space_element)
            space_element = new_config.createTextNode("\n    ")
            new_config.documentElement.insertBefore(space_element, first_author_element)
            # inserisci l'elemento <split>
            split_element = new_config.createElement("split")
            split_element.appendChild(new_config.createTextNode(split))
            new_config.documentElement.insertBefore(split_element, space_element)
        else:
            # inserisci l'unico autore
            author_elements[0].appendChild(new_config.createTextNode(autore))

        # leggi la tracklist
        tracklist = open(oldtracklist, "r").read()
        # rimuovi le linee vuote
        tracklist = filter(lambda x: len(x) != 0, tracklist.splitlines())
        tracklist = reduce(lambda x,y: x + "\n" + y, tracklist)
        # inserisci 4 spazi all'inizio della stringa
        tracklist = "    " + tracklist
        # inserisci 8 spazi alla fine di ogni riga
        tracklist = tracklist.replace("\n", "\n        ")
        # inserisci 4 spazi alla fine della stringa
        tracklist = tracklist + "\n    "
        # converti in Unicode
        tracklist = unicode(tracklist, "utf-8")
        # inserisci la tracklist
        new_config.getElementsByTagName("tracklist")[0].appendChild(new_config.createTextNode(tracklist))

        # scrivi il file
        out = open(METADATA_FILE, "w")
        new_config_string = new_config.toxml().replace("<album>", "\n\n<album>")
        #print new_config_string
        out.write(new_config_string.encode("utf-8"))




class Album:


    def __init__(self, album_dir):

        # inizializza le variabili
        self.directory   = None

        self.author      = None
        self.title       = None
        self.year        = None
        self.genre       = None

        self.is_split    = None
        self.split_index = None

        self.single_disc = None
        self.tracklist   = None

        # prepara il path del file di configurazione e della copertina
        self.directory = album_dir

        # controlla se esiste il file di configurazione
        if not os.path.isfile(self.config_file):
            raise Exception(self.directory + ": Il file contenente i dati dell'album non esiste")

        # controlla se esiste la copertina
        if not os.path.isfile(self.cover_image):
            raise Exception(self.directory + ": La cover non esiste")

        # leggi e valida il file di configurazione
        ALBUM_XSD.assertValid(lxml.etree.parse(self.config_file))
        config = xml.dom.minidom.parse(self.config_file)

        # controlla se l'album e' uno split
        self.split_index = config.getElementsByTagName("split")
        if len(self.split_index) != 0:
            self.is_split = True
            self.split_index = int(self.split_index[0].firstChild.data)
        else:
            self.is_split = False
            self.split_index = None

        # leggi l'autore dell'album
        if self.is_split:
            self.author = []
            author_elements = config.getElementsByTagName("author")
            for author_element in author_elements:
                self.author.append(author_element.firstChild.data)
        else:
            self.author = config.getElementsByTagName("author")[0].firstChild.data
        
        # leggi il titolo dell'album
        self.title = config.getElementsByTagName("title")[0].firstChild.data
        
        # leggi il genere dell'album
        self.genre = config.getElementsByTagName("genre")[0].firstChild.data

        # leggi l'anno di pubblicazione dell'album
        self.year = config.getElementsByTagName("year")[0].firstChild.data

        # controlla se l'album contiene piu' dischi
        tracklist_element = config.getElementsByTagName("tracklist")
        if len(tracklist_element) != 0:
            # l'album contiene un solo disco
            self.single_disc = True
            # leggi il contenuto dell'elemento e mettilo in un array
            self.tracklist = tracklist_element[0].firstChild.data.splitlines()
            # rimuovi gli spazi vuoti all'inizio e alla fine di ogni titolo
            self.tracklist = map(lambda x: x.strip(), self.tracklist)
            # rimuovi le linee vuote
            self.tracklist = filter(lambda x: len(x) != 0 , self.tracklist)
        else:
            # l'album contiene piu' di un disco
            self.single_disc = False
            # la tracklist e' indicizzata con il titolo dei dischi
            self.tracklist = []
            disc_elements = config.getElementsByTagName("disc")
            for disc_element_idx in range(len(disc_elements)):
                disc_element = disc_elements[disc_element_idx]
                # leggi il titolo del disco
                disc_title = disc_element.getAttribute("title")
                # se il titolo del disco non e' definito
                if len(disc_title) == 0:
                    # usa un numero progressivo
                    disc_title = disc_element_idx + 1
                # leggi la tracklist del disco
                self.tracklist.append([disc_title , disc_element.firstChild.data.splitlines()])
                # rimuovi gli spazi vuoti all'inizio e alla fine di ogni titolo
                self.tracklist[-1][1] = map(lambda x: x.strip(), self.tracklist[-1][1])
                # rimuovi le linee vuote
                self.tracklist[-1][1] = filter(lambda x: len(x) != 0 , self.tracklist[-1][1])

        # controlla se il numero di tracce audio corrisponde alla lunghezza
        # della tracklist
        tracklist_length = 0
        if self.single_disc:
            tracklist_length = len(self.tracklist)
        else:
            for disc in self.tracklist:
                tracklist_length += len(disc[1])
        if tracklist_length != len(self.audiofiles):
            #print tracklist_length
            #print len(self.audiofiles)
            raise Exception("Il numero di tracce audio non corrisponde alla lunghezza della tracklist (tracce = " + str(len(self.audiofiles)) + ", tracklist = " + str(tracklist_length) + ")")


    audiofiles  = property(fset = None, fget = lambda self: self.__get_audiofiles())
    config_file = property(fset = None, fget = lambda self: os.path.join(self.directory, METADATA_FILE) )
    cover_image = property(fset = None, fget = lambda self: os.path.join(self.directory, COVER_IMAGE))
    thumbnail_image = property(fset = None, fget = lambda self: os.path.join(self.directory, THUMBNAIL_IMAGE))


    def check_unknown_files(self):

        '''Cerca i file sconosciuti'''

        print_header("Controllo i file sconosciuti")
        
        # cerca i file sconosciuti nella directory dell'album
        unknown = []
        for item in os.listdir(self.directory):
            if item != METADATA_FILE and item != COVER_IMAGE and item != THUMBNAIL_IMAGE and mimetypes.guess_type(item)[0] not in VALID_MIME_TYPES:
                unknown.append(item)

        # se ci sono dei file sconosciuti
        if len(unknown) != 0:
            # stampa l'intestazione del messaggio
            for item in unknown:
                print_item(item)


    def check_filenames(self):

        '''Controlla se i nomi dei file e della directory dell'album sono coerenti
        con il file di configurazione'''

        print_header("Controllo i nomi dei file")

        # calcola il nome corretto della directory dell'album
        if self.is_split:
            new_album_dir = ""
            for author in self.author:
                new_album_dir += author + " & "
            new_album_dir = new_album_dir[0:-3]
            new_album_dir = os.path.join(os.path.split(self.directory)[0], sanitize(new_album_dir + " [" + self.year + "] " + self.title))
        else:
            new_album_dir = os.path.join(os.path.split(self.directory)[0], sanitize(self.author + " [" + self.year + "] " + self.title))

        # elimina l'eventuale punto ala fine del nome della directory
        if new_album_dir[-1] == ".":
            new_album_dir = new_album_dir[:-1] + "_"
            
        # controlla se la directory corrente dell'album e' diversa da quella calcolata
        if self.directory != new_album_dir:
            # rinomina la directory dell'album
            print_item("Album directory:  '" + os.path.split(self.directory)[1] + "'  -->  '" + os.path.split(new_album_dir)[1] + "'")
            os.rename(self.directory, new_album_dir)
            self.directory = new_album_dir

        # se l'album ha un solo disco
        if self.single_disc:
            # usa la tracklist letta dal file
            tracklist = self.tracklist
        else:
            # prepara una tracklist unificata
            tracklist = []
            for disc_tracklist in self.tracklist:
                tracklist += disc_tracklist[1]
        
        # controlla se i nomi dei file audio sono corretti
        audiofiles = self.audiofiles
        for item in range(len(tracklist)):
            # estrai l'estensione del file
            file_extension = os.path.splitext(os.path.split(audiofiles[item])[1])[1][1:]
            # calcola il nome corretto del file
            new_track_name = os.path.join(self.directory, str(str(item + 1)).zfill(2) + "." + sanitize(tracklist[item])) + "." + file_extension
            # se il nome attuale e' diverso dal nome corrente
            if new_track_name != audiofiles[item]:
                #print type(new_track_name)
                #print type(audiofiles[item])
                #for x in range(len(new_track_name)):
                #    if new_track_name[x] != audiofiles[item][x]:
                #        print new_track_name[x] + " <> " + audiofiles[item][x]
                #    #print x
                #    #print new_track_name[x]
                #print repr(new_track_name) != audiofiles[item]
                print_item("'" + os.path.split(audiofiles[item])[1] + "  -->  '" + os.path.split(new_track_name)[1] + "'")
                # rinomina il file
                os.rename(audiofiles[item], new_track_name)

    def create_thumbnail(self):

        '''Crea la miniatura della cover (64x64)'''

        dest_size = 64
        dest_width = dest_size
        dest_height = dest_size

        cover = Image.open(self.cover_image)
        (width, height) = cover.size
        ratio = dest_width / dest_height

        if (ratio < 1):
            dest_width = dest_height * ratio
        else:
            dest_height = dest_width / ratio

        thumb = cover.resize((dest_width, dest_height), Image.ANTIALIAS)
        thumb.save(self.thumbnail_image)

    def check_metadata(self):

        '''Controlla i metadati dei file audio'''

        print_header("Controllo i metadati")
        
        # se l'album ha un solo disco
        if self.single_disc:
            # usa la tracklist letta dal file
            tracklist = self.tracklist
        else:
            # prepara una tracklist unificata
            tracklist = []
            for disc in self.tracklist:
                disc_title = disc[0]
                for track in disc[1]:
                    tracklist.append([disc_title , track])

        for idx in range(len(self.audiofiles)):
            print_item("'" + os.path.split(self.audiofiles[idx])[1] + "'")
            # apri il file con mutagen
            if mimetypes.guess_type(self.audiofiles[idx])[0] == "audio/mpeg":
                easy_mode = True
            else:
                easy_mode = False
            item = mutagen.File(self.audiofiles[idx], easy = easy_mode)
            # cancella i vecchi tag
            item.delete()
            # se l'album e' uno split
            if self.is_split:
                # se l'indice dell'elemento attuale e' minore (solo minore
                # perche' idx parte da zero) all'indice dello split
                if idx < self.split_index:
                    # usa il nome del primo autore
                    item["artist"] = self.author[0]
                else:
                    # usa il nome del secondo autore
                    item["artist"] = self.author[1]
            else:
                # c'e' un solo autore, usa quello
                item["artist"] = self.author
            item["album"] = self.title
            # se l'album ha un solo disco
            if self.single_disc:
                item["title"] = tracklist[idx]
            else:
                item["title"] = tracklist[idx][1]
                # inserisci anche il titolo del disco
                # convertito a stringa per i dischi che non hanno un proprio titolo,
                # ma non se il file e' un MP4
                if not isinstance(item, mutagen.mp4.MP4):
                    item["discsubtitle"] = str(tracklist[idx][0])
            item["genre"] = self.genre
            item["date"] = self.year
            item["tracknumber"] = unicode(str(idx + 1) + "/" + str(len(tracklist)))
            # salva il file
            item.save()
            # se il file e' un mp3
            if isinstance(item, mutagen.mp3.EasyMP3):
                # crea il frame ID3 contenente l'immagine
                item_image = mutagen.id3.APIC(encoding = 3, mime = 'image/jpeg', type = 3, desc = 'Front cover', data = open(self.cover_image, "rb").read())
                item = mutagen.id3.ID3(self.audiofiles[idx])
                # aggiungilo al file
                item.add(item_image)
                # salva il file
                item.save()
            elif isinstance(item, mutagen.mp4.MP4):
                # assegna la copertina
                item["covr"] = [ mutagen.mp4.MP4Cover(open(self.cover_image, "rb").read()) ]
                # salva il file
                item.save()


    def check_crlf(self):

        '''Converte il file di configurazione in formato DOS'''

        # leggi il contenuto del file
        config_data = open(self.config_file, "r").read().splitlines()

        # sostituisci i delimitatori di fine linea con la versione DOS
        config_data = map(lambda line: line + "\r\n", config_data)

        # scrivi il file convertito
        out = open(self.config_file, "w")

        # scrivi il file
        out.write(reduce(lambda x,y: x + y, config_data))


    def check(self):

        '''Esegue tutti i controlli di consistenza sull'album'''

        print(termcolor.colored('### ', 'blue', attrs = [ 'bold' ]) + os.path.split(self.directory)[1])
        
        # esegui tutti i controlli
        self.check_filenames()
        self.check_metadata()
        self.check_unknown_files()
        self.check_crlf()
        
        # temporarily disabled: jpeg support not available
        #self.create_thumbnail()
        

    def __get_audiofiles(self):

        # trova tutti i file audio
        audiofiles = []
        for trackfilename in os.listdir(self.directory):
            trackfilename = os.path.join(self.directory, trackfilename)
            if os.path.isfile(trackfilename) and mimetypes.guess_type(trackfilename)[0] in VALID_MIME_TYPES:
                audiofiles.append(trackfilename)
        audiofiles.sort()
        return audiofiles


###########
# ACTIONS #
###########


class ActionExecutor:


    '''Execute the action selected by the command line'''

    
    def print_genres(self, args):
    
        print(os.linesep.join(VALID_GENRES))


    def print_commands(self, args):

        print(os.linesep.join([ name for name in self.__class__.__dict__ if inspect.ismethod(getattr(self.__class__, name)) ]))


    def init_album(self, args):
    
        '''Initialize the current directory with the needed configuration files'''
    
        # @TODO: automatically convert
        # http://code.activestate.com/recipes/66434-change-line-endings/
    
        if not os.path.isdir(args.path):
            raise argparse.ArgumentError("'{0}' is not a valid path".format(args.path))

        if not os.access(args.path, os.R_OK):
            raise argparse.ArgumentError("'{0}' is not a readable dir".format(args.path))

        # determine the path to the metadata file
        metadata_file = os.path.join(os.path.realpath(args.path), METADATA_FILE)
    
        # if the file does not exist
        if not os.path.isfile(metadata_file):
            
            # create it
            out = open(metadata_file, 'w')
            
            # ensure it has DOS line endings
            for item in METADATA_XML_TEMPLATE.splitlines():
                
                out.write(item + "\r\n")


    def check_album(self, args):

        '''Perform a consistency check on the given album'''
    
        if not os.path.isdir(args.path):
            raise argparse.ArgumentError("'{0}' is not a valid path".format(args.path))

        if not os.access(args.path, os.R_OK):
            raise argparse.ArgumentError("'{0}' is not a readable dir".format(args.path))

        # determine the path to the metadata file
        path = unicode(os.path.realpath(args.path), "utf-8")

        # create the Album object
        Album(path).check()


    def check_library(self, args):

        '''Perform a consistency check on the given library'''
    
        if not os.path.isdir(args.path):
            raise argparse.ArgumentError("'{0}' is not a valid path".format(args.path))

        if not os.access(args.path, os.R_OK):
            raise argparse.ArgumentError("'{0}' is not a readable dir".format(args.path))

        # for each item in the given path
        for item in os.listdir(args.path):
            
            # if the item is directory
            if os.path.isdir(item):
                
                # perform the check
                Album(os.path.join(args.path, item)).check()


    def test(self, args):

        '''Test the progamme (used for debugging)'''

        # check if the global variables contain Unicode strings
        print("### Checking global variables")
        g = globals()
        for key in g:
            if type(g[key]) == str:
                print("Non-Unicode string: " + key)

        # create a temporary album
        tmp_album_dir = unicode(tempfile.mkdtemp(prefix = "musyc-"), "UTF-8")
        self.targetdir = tmp_album_dir
        
        # create an empty cover
        open(os.path.join(self.targetdir, COVER_IMAGE), "w").close()
        
        # create an empty track
        open(os.path.join(self.targetdir, "prova.mp3"), "w").close()
        
        # create the configuration file, containing meaningless values, but still valid
        config = xml.dom.minidom.parseString(METADATA_XML_TEMPLATE)
        
        # insert the title
        title_element = config.getElementsByTagName("title")[0]
        title_element.appendChild(config.createTextNode("Titolo"))
        
        # insert the year
        config.getElementsByTagName("year")[0].appendChild(config.createTextNode("2000"))
        
        # insert the genre
        config.getElementsByTagName("genre")[0].appendChild(config.createTextNode("Rock"))
        
        # insert the author
        config.getElementsByTagName("author")[0].appendChild(config.createTextNode("Autore"))
        
        # insert a track
        config.getElementsByTagName("tracklist")[0].appendChild(config.createTextNode("Traccia_1\n"))
        out = open(os.path.join(self.targetdir, METADATA_FILE), "w")
        config_string = config.toxml()
        out.write(config_string)
        out.close()

        # execute a complete check on the just created album
        print("### Checking the variables of a temporary album")
        
        print("Album name: " + self.targetdir)
        print("Content:")
        for f in os.listdir(tmp_album_dir):
            print("- " + f)
            
        print("Performing checks:")
        album = Album(self.targetdir)
        for key in album.__dict__:
            if type(album.__dict__[key]) == str:
                print("Non-Unicode strings: " + key)
            elif album.__dict__[key] == None:
                print("Empty:               " + key)
        shutil.rmtree(tmp_album_dir)


########################
# COMMAND LINE PARSING #
########################


class ArgumentParser(argparse.ArgumentParser):
    
    
    '''Parser for the command line arguments of the program'''
    
    
    def __init__(self, *args, **kwargs):
        
        kwargs = { 'prog' : __prog__, 'description' : __description__, 'version' : __version__ }
        super(ArgumentParser, self).__init__(**kwargs)


    def parse(self):
        
        ns = ActionExecutor()
        
        if not hasattr(self, 'subparsers'):
            self.subparsers = self.add_subparsers(title = 'subcommands', help = 'Additional help')

            init_parser = self.subparsers.add_parser('init')
            init_parser.add_argument('--path', help = 'Specify target path', default = '.')
            init_parser.set_defaults(func = ns.init_album)
        
            check_parser = self.subparsers.add_parser('check')
            check_parser.add_argument('--path', help = 'Specify target path', default = '.')
            check_parser.set_defaults(func = ns.check_album)
        
            check_parser = self.subparsers.add_parser('checklibrary')
            check_parser.add_argument('--path', help = 'Specify target path', default = '.')
            check_parser.set_defaults(func = ns.check_library)
        
            check_parser = self.subparsers.add_parser('genres')
            check_parser.set_defaults(func = ns.print_genres)
        
            check_parser = self.subparsers.add_parser('commands')
            check_parser.set_defaults(func = ns.print_commands)
        
            check_parser = self.subparsers.add_parser('test')
            check_parser.set_defaults(func = ns.test)
        
        args = self.parse_args(sys.argv[1:], ns)
        args.func(args)


########
# MAIN #
########


if __name__ == "__main__":

    try:
        ArgumentParser().parse()

    except Exception, e:

        # print an error message
        print(termcolor.colored('!!! ', 'red', attrs = [ 'bold' ]) + unicode(e))

        # print the stack trace
        traceback.print_exc(file = sys.stdout)

        # exit to the system, returning an error
        sys.exit(1)